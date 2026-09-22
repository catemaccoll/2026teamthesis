## load packages 
# EACH TIME YOU RESTART R, make sure to run the this section - there's no harm to running it every time  ---#
library(lme4)
library(dplyr)
library(tidyr)
library(ggplot2)
library(emmeans)
library(car)
library(broom.mixed)
library(officer)
library(flextable)
library(lmerTest)
#---#


## clearing your workspace 
# every time you run the script, start from here (or select all)
# this clears your workspace (all of the information R has stored), and helps ensure no errors get carried forward 
rm(list = ls())

## setup your working directory and files
# IF THIS IS A NEW SCRIPT VERSION - change the line below to your working directory in the double quotations
# make sure there aren't single quotations as well, and you've replaced backslashes if you're on a PC
setwd("/Users/chloetalbot/Desktop/PSYC4091")

## read in your data file

# it's fine to leave this as just data, but if you import a different file, it will override each time
# if you need multiple data files, you might want to rename them as data1, data2, etc. 
# (but will need to also change instances of "data" to data1, etc. below)
# if you get an error on this line, check that there is a file in the working directory specified above called "aggregate.csv
data <- read.csv("aggregate.csv")
# print(data.frame(variable = names(data), type = sapply(data, function(x) class(x)[1])), row.names = FALSE)


## check that you've correctly imported it and get some information 
# note: you will need to change the name "data" if you've assigned a different name (see above) 
print(data) # print the first 22 rows of your data 
print(colnames(data)) # give me the names of the variables
print(nrow(data)) # how many rows are in it

############ (2) HELPER FUNCTIONS & DICTIONARIES ARE DEFINED HERE, DON'T EDIT WITHOUT CHECKING ############ 


## helper functions are defined here (don't edit)
# NOTE 1:you will need to run this section each time you restart R or clear your workspace
# when you run this you should get lots of text in blue in the console (below) without any errors 
# NOTE 2: I will not be checking this section, so if you (or an artificial friend) changes anything in section 2,
# so any resultant errors in your analyses will go undetected --------#

# these need to be run before the sections below so that the functions you call have been defined. 
# if you get any errors, check that they have 


## filtering your data 
# create a new dataset containing only the row/s matching one (or more) levels of a variable
# level can be a single value, or a vector like c("feedback", "searchtermination") to keep more than one
filter_by_level <- function(data, filter_var, level) {
  stopifnot(filter_var %in% names(data))
  
  # warn if a level you asked for doesn't actually exist (usually a typo)
  present_levels <- unique(data[[filter_var]])
  missing_levels <- setdiff(level, present_levels)
  if (length(missing_levels) > 0) {
    cat(sprintf("\nWarning: %s not found in '%s'. Available levels are:\n",
                paste(missing_levels, collapse = ", "), filter_var))
    print(present_levels)
  }
  
  n_before <- nrow(data)
  filtered_data <- data %>% filter(.data[[filter_var]] %in% level)
  
  cat(sprintf("\nFiltered to %s = %s: %d row(s) kept out of %d (%d removed)\n",
              filter_var, paste(level, collapse = ", "),
              nrow(filtered_data), n_before, n_before - nrow(filtered_data)))
  
  return(filtered_data)
}


## descriptives and frequencies 
# use get_descriptives() for continuous variables (e.g., choiceRT, confidence, survey scores)
# use get_frequencies() for categorical variables (e.g., task_name, gender_prolific)

# collapse to one row per participant before summarising,
# so person-level variables count each participant rather than each trials
# warns if a variable isn't actually constant within an ID
.collapse_one_row_per <- function(data, vars, id_col) {
  stopifnot(id_col %in% names(data))
  vars <- setdiff(unique(vars), id_col)
  
  missing_vars <- setdiff(vars, names(data))
  if (length(missing_vars) > 0) {
    stop(sprintf("Variable(s) not found in the data: %s", paste(missing_vars, collapse = ", ")))
  }
  
  for (v in vars) {
    varies <- data %>%
      group_by(across(all_of(id_col))) %>%
      summarise(n_vals = n_distinct(.data[[v]][!is.na(.data[[v]])]), .groups = "drop") %>%
      filter(n_vals > 1)
    
    if (nrow(varies) > 0) {
      cat(sprintf("\nWarning: '%s' takes more than one value within %d %s(s) - the first non-missing value was used. Check: %s\n",
                  v, nrow(varies), id_col, paste(head(varies[[id_col]], 5), collapse = ", ")))
    }
  }
  
  out <- data %>%
    group_by(across(all_of(id_col))) %>%
    summarise(across(all_of(vars), ~ {
      vals <- .x[!is.na(.x)]
      if (length(vals) == 0) .x[NA_integer_] else vals[1]   # keeps the column's type
    }), .groups = "drop")
  
  cat(sprintf("\nOne row per %s: %d kept from %d row(s)\n", id_col, nrow(out), nrow(data)))
  out
}

## descriptives - continuous variables (one row per variable; add group_var to split by another variable's levels)
.make_descriptives_data <- function(data, vars, group_var = NULL, one_row_per = NULL) {
  
  # collapse first, so everything below runs on one row per participant
  if (!is.null(one_row_per)) {
    data <- .collapse_one_row_per(data, c(vars, group_var), one_row_per)
  }
  
  if (is.null(group_var)) {
    return(bind_rows(lapply(vars, function(v) {
      x <- data[[v]]
      if (!is.numeric(x)) {
        stop(sprintf("'%s' isn't numeric - descriptives are for continuous variables (try get_frequencies() for categorical ones).", v))
      }
      data.frame(
        Variable = v,
        N        = sum(!is.na(x)),
        Missing  = sum(is.na(x)),
        M        = round(mean(x, na.rm = TRUE), 2),
        SD       = round(sd(x, na.rm = TRUE), 2),
        Min      = round(min(x, na.rm = TRUE), 2),
        Max      = round(max(x, na.rm = TRUE), 2),
        stringsAsFactors = FALSE
      )
    })))
  }
  
  stopifnot(group_var %in% names(data))
  
  n_na_group <- sum(is.na(data[[group_var]]))
  if (n_na_group > 0) {
    cat(sprintf("\nNote: %d row(s) have a missing '%s' and are excluded from the by-group breakdown.\n",
                n_na_group, group_var))
  }
  
  group_levels <- sort(unique(data[[group_var]]))
  
  bind_rows(lapply(group_levels, function(g) {
    sub_data <- data[!is.na(data[[group_var]]) & data[[group_var]] == g, ]
    sub_desc <- .make_descriptives_data(sub_data, vars)  # reuse the calculation above, just on this slice
    sub_desc[[group_var]] <- g
    sub_desc[, c(group_var, setdiff(names(sub_desc), group_var))]
  }))
}


# NA-out target columns in rows where a flag column equals a given value
# (e.g. too_slow == 1 -> choice, choiceRT become NA)
# NA-out target columns in rows where a flag column equals a given value,
# and optionally NA-out the matching n-1 columns on the FOLLOWING row
na_out_flagged_rows <- function(df, flag_col, flag_value, target_cols,
                                lag_cols   = NULL,   # e.g. c("prevConfidence", "prevChoiceRT")
                                group_cols = c("subject", "trialIndex"),
                                order_col  = "stepIndex") {
  flagged <- df[[flag_col]] == flag_value
  flagged[is.na(flagged)] <- FALSE  # unknown flag values are left untouched
  
  df <- df %>% mutate(across(all_of(target_cols), ~ replace(.x, flagged, NA)))
  
  if (is.null(lag_cols)) return(df)
  
  missing <- setdiff(c(lag_cols, group_cols, order_col), names(df))
  if (length(missing) > 0) {
    stop(sprintf("Column(s) not found in the data: %s", paste(missing, collapse = ", ")))
  }
  
  df$.flagged <- flagged
  df$.row_id  <- seq_len(nrow(df))   # so we can put the rows back in their original order
  
  df <- df %>%
    arrange(across(all_of(c(group_cols, order_col)))) %>%
    group_by(across(all_of(group_cols))) %>%          # lag can't spill across trials/participants
    mutate(.prev_flagged = coalesce(lag(.flagged), FALSE)) %>%
    ungroup()
  
  n_carried <- sum(df$.prev_flagged)
  
  df <- df %>%
    mutate(across(all_of(lag_cols), ~ replace(.x, .prev_flagged, NA))) %>%
    arrange(.row_id) %>%
    select(-.row_id, -.flagged, -.prev_flagged)
  
  cat(sprintf("\nCarried forward to n+1: %d row(s), column(s): %s\n",
              n_carried, paste(lag_cols, collapse = ", ")))
  return(df)
}

# print descriptives to the console for a quick look (add group_var to split by another variable)
get_descriptives <- function(data, vars, group_var = NULL, one_row_per = NULL) {
  desc <- .make_descriptives_data(data, vars, group_var = group_var, one_row_per = one_row_per)
  cat("\n--- Descriptive statistics ---\n")
  print(desc, row.names = FALSE)
  invisible(desc)
}

# APA table of descriptive statistics (optionally split by levels of group_var)
apa_descriptives_table <- function(data, vars, group_var = NULL, one_row_per = NULL,
                                   title = "Descriptive Statistics",
                                   note  = "M = mean, SD = standard deviation. N = valid (non-missing) responses.") {
  desc <- .make_descriptives_data(data, vars, group_var = group_var, one_row_per = one_row_per)
  
  # make the table note honest about what N counts
  if (!is.null(one_row_per)) {
    note <- paste(note, sprintf("One row per %s.", one_row_per))
  }
  
  ft <- .apa_flextable(desc, title = title, note = note)
  print(ft)
  invisible(ft)
}

# calculate frequencies
.make_frequencies_data <- function(data, var) {
  x   <- data[[var]]
  tab <- table(x) # excludes NA by default, and keeps numbers in numeric (not alphabetical) order
  
  freq <- data.frame(
    Level = names(tab),
    n     = as.integer(tab),
    stringsAsFactors = FALSE
  )
  
  n_missing <- sum(is.na(x))
  if (n_missing > 0) {
    freq <- bind_rows(freq, data.frame(Level = "Missing", n = n_missing, stringsAsFactors = FALSE))
  }
  
  freq %>% mutate(Percent = round(100 * n / sum(n), 2))
}

# print frequency table to the console
get_frequencies <- function(data, vars, max_levels = 30, one_row_per = NULL) {
  if (!is.null(one_row_per)) data <- .collapse_one_row_per(data, vars, one_row_per)
  
  results <- list()
  for (v in vars) {
    if (length(unique(data[[v]])) > max_levels) {
      cat(sprintf("\nNote: '%s' has more than %d unique values - check this is the variable you meant (get_descriptives() may suit continuous variables better).\n",
                  v, max_levels))
    }
    freq <- .make_frequencies_data(data, v)
    cat(sprintf("\n--- Frequencies: %s ---\n", v))
    print(freq, row.names = FALSE)
    results[[v]] <- freq
  }
  invisible(results)
}

# APA table of frequencies for a categorical variable
apa_frequencies_table <- function(data, var, title = NULL, one_row_per = NULL,
                                  note = "Percentages are calculated out of the total N (including any missing responses).") {
  if (is.null(title)) title <- paste("Frequency of", var)
  if (!is.null(one_row_per)) {
    data <- .collapse_one_row_per(data, var, one_row_per)
    note <- paste(note, sprintf("One row per %s.", one_row_per))
  }
  freq <- .make_frequencies_data(data, var)
  ft <- .apa_flextable(freq, title = title, note = note)
  print(ft)
  invisible(ft)
}

## group level outliers 
# flag group level outliers 
flag_group_outliers <- function(data, rt_col = "choiceRT", subject_col = "subject", n_sd = 3) {
  participant_rt <- data %>%
    group_by(across(all_of(subject_col))) %>%
    summarise(mean_rt = mean(.data[[rt_col]], na.rm = TRUE), .groups = "drop") %>%
    mutate(
      group_mean         = mean(mean_rt, na.rm = TRUE),
      group_sd           = sd(mean_rt,   na.rm = TRUE),
      rt_outlier_subject = abs(mean_rt - group_mean) > n_sd * group_sd
    )
  return(participant_rt)
}

# print group level outliers 
print_group_outliers <- function(participant_rt) {
  cat("\n--- Participant-level RT outliers ---\n")
  print(participant_rt)          
  cat("\nFlagged participants:\n")
  flagged <- filter(participant_rt, rt_outlier_subject)
  if (nrow(flagged) == 0) cat("  (none)\n") else print(flagged)   # same here
  invisible(flagged)
}

# remove group level outliers 
remove_group_outliers <- function(data, participant_rt, subject_col = "subject") {
  flagged <- filter(participant_rt, rt_outlier_subject)[[subject_col]]
  n_before <- nrow(data)
  data <- data %>% filter(!.data[[subject_col]] %in% flagged)
  cat(sprintf("\nGroup outliers removed: %d participant(s), %d row(s) dropped\n",
              length(flagged), n_before - nrow(data)))
  return(data)
}


## printing values
report_value_counts <- function(df, var, value, id_col = NULL,
                                label = deparse(substitute(df)), show_zero = FALSE) {
  
  if (!var %in% names(df)) {
    message("No column called ", var); return(invisible(NULL))
  }
  
  x <- df[[var]]
  
  # numeric comparison when both sides look numeric, otherwise trimmed text
  num_x   <- suppressWarnings(as.numeric(as.character(x)))
  num_val <- suppressWarnings(as.numeric(as.character(value)))
  if (!all(is.na(num_x)) && !any(is.na(num_val))) {
    matched <- num_x %in% num_val
  } else {
    matched <- trimws(as.character(x)) %in% trimws(as.character(value))
  }
  matched[is.na(matched)] <- FALSE
  
  n_hits  <- sum(matched)
  val_lbl <- paste(value, collapse = " | ")
  
  if (is.null(id_col) || !id_col %in% names(df)) {
    message(sprintf("\n%s -- %s == %s: %d of %d rows (%.1f%%)",
                    label, var, val_lbl, n_hits, nrow(df), 100 * n_hits / nrow(df)))
    return(invisible(NULL))
  }
  
  ids <- df[[id_col]]
  message(sprintf("\n%s -- %s == %s: %d of %d rows (%.1f%%), %d participant(s) affected",
                  label, var, val_lbl, n_hits, nrow(df), 100 * n_hits / nrow(df),
                  length(unique(ids[matched]))))
  
  n_rows <- tapply(matched, ids, length)
  hits   <- tapply(matched, ids, sum)
  
  per_ppt <- data.frame(
    id     = names(hits),
    n_rows = as.integer(n_rows),
    n_hits = as.integer(hits),
    prop   = round(as.integer(hits) / as.integer(n_rows), 3),
    stringsAsFactors = FALSE
  )
  names(per_ppt)[1] <- id_col
  
  if (!show_zero) per_ppt <- per_ppt[per_ppt$n_hits > 0, , drop = FALSE]
  per_ppt <- per_ppt[order(-per_ppt$n_hits), , drop = FALSE]
  
  print(per_ppt, row.names = FALSE)
  invisible(per_ppt)
}

## cleaning trial level outliers  
# flag trial level outliers 
flag_trial_outliers <- function(data, rt_col = "choiceRT", subject_col = "subject", n_sd = 3) {
  data <- data %>%
    group_by(across(all_of(subject_col))) %>%
    mutate(
      rt_mean_subj     = mean(.data[[rt_col]], na.rm = TRUE),
      rt_sd_subj       = sd(.data[[rt_col]],   na.rm = TRUE),
      rt_outlier_trial = abs(.data[[rt_col]] - rt_mean_subj) > n_sd * rt_sd_subj
    ) %>%
    ungroup()
  return(data)
}

# print trial level outliers 
print_trial_outliers <- function(data, subject_col = "subject") {
  summary <- data %>%
    group_by(across(all_of(subject_col))) %>%
    summarise(
      n_trials         = n(),
      n_outlier_trials = sum(rt_outlier_trial, na.rm = TRUE),
      pct_outlier      = round(100 * n_outlier_trials / n_trials, 1),
      .groups          = "drop"
    )
  cat("\n--- Trial-level RT outliers ---\n")
  print(summary, row.names = FALSE)
  invisible(summary)
}

# remove trial level outliers
remove_trial_outliers <- function(data,
                                  mode       = "rt_only",
                                  rt_col     = "choiceRT",
                                  extra_cols = c("choice", "choiceRT", "confidence")) {
  stopifnot("rt_outlier_trial" %in% names(data))
  
  if (mode == "rt_only") {
    na_cols <- rt_col
  } else if (mode == "all") {
    na_cols <- unique(c(rt_col, extra_cols))
  } else {
    stop("`mode` must be 'rt_only' or 'all'")
  }
  
  # Only NA columns that actually exist
  na_cols <- intersect(na_cols, names(data))
  
  data <- data %>%
    mutate(across(all_of(na_cols),
                  ~ replace(.x, rt_outlier_trial %in% TRUE, NA)))
  
  cat(sprintf("\nTrial outliers: set to NA in column(s): %s\n  (rows retained)\n",
              paste(na_cols, collapse = ", ")))
  return(data)
}


## standardising variables 
# this function can be used to standardise your variables for analysis
standardise <- function(x) {
  as.numeric((x - mean(x, na.rm = TRUE)) / sd(x, na.rm = TRUE))
}


## outputs 
# this will give us the fixed effects table/s - categorical DV version 
.make_fixed_effects_data <- function(model) {
  coef_tab <- summary(model)$coefficients
  data.frame(
    term      = rownames(coef_tab),
    estimate  = coef_tab[, "Estimate"],
    se        = coef_tab[, "Std. Error"],
    stringsAsFactors = FALSE
  ) %>%
    mutate(
      Wald_ChiSq = (estimate / se)^2,
      p_raw      = pchisq(Wald_ChiSq, df = 1, lower.tail = FALSE),
      OR         = exp(estimate),
      OR_lower   = exp(estimate - 1.96 * se),
      OR_upper   = exp(estimate + 1.96 * se)
    ) %>%
    mutate(p = ifelse(p_raw < .001, "< .001", sub("^0", "", sprintf("%.3f", p_raw)))) %>%
    mutate(across(where(is.numeric), ~ round(.x, 2))) %>%
    select(-p_raw)
}

## this will give us the fixed effects table/s - continuous DV version 
.make_fixed_effects_data_lmer <- function(model) {
  coef_tab <- summary(model)$coefficients
  data.frame(
    term     = rownames(coef_tab),
    estimate = coef_tab[, "Estimate"],
    se       = coef_tab[, "Std. Error"],
    df       = coef_tab[, "df"],
    t_value  = coef_tab[, "t value"],
    p_raw    = coef_tab[, "Pr(>|t|)"],
    stringsAsFactors = FALSE
  ) %>%
    mutate(
      CI_lower = estimate - 1.96 * se,
      CI_upper = estimate + 1.96 * se
    ) %>%
    mutate(p = ifelse(p_raw < .001, "< .001", sub("^0", "", sprintf("%.3f", p_raw)))) %>%
    mutate(across(where(is.numeric), ~ round(.x, 2))) %>%
    select(-p_raw)
}

# this will give us APA formatting 
.apa_flextable <- function(data, title = "", note = "") {
  ft <- flextable(data) %>%
    # Title as a caption (bold, above table)
    set_caption(caption = title) %>%
    
    # Align header and body
    align(align = "left",  part = "header") %>%
    align(align = "left",  j = 1, part = "body") %>%
    align(align = "right", j = 2:ncol(data), part = "body") %>%
    
    # APA font
    font(fontname = "Times New Roman", part = "all") %>%
    fontsize(size = 12, part = "all") %>%
    
    # Bold header row
    bold(part = "header") %>%
    
    # APA borders: thick top & bottom of header, thin below header
    border_remove() %>%
    hline_top(part = "header",
              border = fp_border_default(width = 1.5)) %>%
    hline(part = "header",
          border = fp_border_default(width = 0.75)) %>%
    hline_bottom(part = "body",
                 border = fp_border_default(width = 1.5)) %>%
    
    # No vertical lines (APA)
    autofit()
  
  # Add note below table if provided
  if (nzchar(note)) {
    ft <- add_footer_lines(ft, values = paste("Note.", note)) %>%
      italic(part = "footer") %>%
      font(fontname = "Times New Roman", part = "footer") %>%
      fontsize(size = 12, part = "footer")
  }
  
  ft
}


## model step 1 function (main effects) - categorical DV version
# this function will give you a model with just main effects and print the summary
fit_main_effects <- function(dv,
                             fixed_effects,
                             random_terms,
                             data,
                             progress = TRUE,
                             family  = binomial(link = "logit"),
                             control = glmerControl(optimizer = "bobyqa",
                                                    optCtrl   = list(maxfun = 2e5)),
                             ...) {
  fixed_part  <- paste(fixed_effects, collapse = " + ")
  random_part <- paste(random_terms,  collapse = " + ")
  fmla        <- as.formula(paste0(dv, " ~ ", fixed_part, " + ", random_part))
  
  cat("\n[Step 1] Main effects model:\n ")
  cat(deparse(fmla), "\n")
  
  # progress print 
  cat("\nFitting model. The numbers below are the optimiser working -- R is fine, don't stress \n",
      "Started ", format(Sys.time(), "%H:%M:%S"), "\n", sep = "")
  utils::flush.console()
  started <- Sys.time()
  
  model <- glmer(fmla, data = data, family = family, control = control,
                 verbose = if (progress) 1L else 0L, ...)
  
  elapsed <- as.numeric(difftime(Sys.time(), started, units = "secs"))
  cat(sprintf("\nDone in %s\n",
              if (elapsed < 60) sprintf("%.0f seconds", elapsed)
              else sprintf("%.1f minutes", elapsed / 60)))
  
  cat("\n--- Summary ---\n")
  print(summary(model))
  invisible(model)
}


## model step 2 function (interaction) - categorical DV version
# this function will give you the second model and print the summary
fit_interactions <- function(dv,
                             fixed_effects,
                             interaction_terms,
                             random_terms,
                             data,
                             progress = TRUE,
                             family  = binomial(link = "logit"),
                             control = glmerControl(optimizer = "bobyqa",
                                                    optCtrl   = list(maxfun = 2e5)),
                             ...) {
  fixed_part       <- paste(fixed_effects,     collapse = " + ")
  interaction_part <- paste(interaction_terms, collapse = " + ")
  random_part      <- paste(random_terms,      collapse = " + ")
  fmla             <- as.formula(paste0(dv, " ~ ",
                                        fixed_part, " + ",
                                        interaction_part, " + ",
                                        random_part))
  
  cat("\n[Step 2] Interactions model:\n ")
  cat(deparse(fmla), "\n")
  
  # progress print 
  cat("\nFitting model. The numbers below are the optimiser working -- R is fine, don't stress \n",
      "Started ", format(Sys.time(), "%H:%M:%S"), "\n", sep = "")
  utils::flush.console()
  started <- Sys.time()
  
  model <- glmer(fmla, data = data, family = family, control = control,
                 verbose = if (progress) 1L else 0L, ...)
  
  elapsed <- as.numeric(difftime(Sys.time(), started, units = "secs"))
  cat(sprintf("\nDone in %s\n",
              if (elapsed < 60) sprintf("%.0f seconds", elapsed)
              else sprintf("%.1f minutes", elapsed / 60)))
  
  cat("\n--- Summary ---\n")
  print(summary(model))
  invisible(model)
}


## model step 1 function (main effects) - continuous DV version
# uses lmer() instead of glmer(), no family argument
fit_main_effects_lmer <- function(dv,
                                  fixed_effects,
                                  random_terms,
                                  data,
                                  progress = TRUE,
                                  REML    = TRUE,
                                  control = lmerControl(optimizer = "bobyqa",
                                                        optCtrl   = list(maxfun = 2e5)),
                                  ...) {
  fixed_part  <- paste(fixed_effects, collapse = " + ")
  random_part <- paste(random_terms,  collapse = " + ")
  fmla        <- as.formula(paste0(dv, " ~ ", fixed_part, " + ", random_part))
  
  cat("\n[Step 1] Main effects model (continuous DV):\n ")
  cat(deparse(fmla), "\n")
  
  # progress print 
  cat("\nFitting model. The numbers below are the optimiser working -- R is fine, don't stress \n",
      "Started ", format(Sys.time(), "%H:%M:%S"), "\n", sep = "")
  utils::flush.console()
  started <- Sys.time()
  
  model <- lmerTest::lmer(fmla, data = data, REML = REML, control = control,
                          verbose = if (progress) 1L else 0L, ...)
  
  elapsed <- as.numeric(difftime(Sys.time(), started, units = "secs"))
  cat(sprintf("\nDone in %s\n",
              if (elapsed < 60) sprintf("%.0f seconds", elapsed)
              else sprintf("%.1f minutes", elapsed / 60)))
  
  cat("\n--- Summary ---\n")
  print(summary(model))
  invisible(model)
}


## model step 2 function (interaction) - continuous DV version
fit_interactions_lmer <- function(dv,
                                  fixed_effects,
                                  interaction_terms,
                                  random_terms,
                                  data,
                                  progress = TRUE,
                                  REML    = TRUE,
                                  control = lmerControl(optimizer = "bobyqa",
                                                        optCtrl   = list(maxfun = 2e5)),
                                  ...) {
  fixed_part       <- paste(fixed_effects,     collapse = " + ")
  interaction_part <- paste(interaction_terms, collapse = " + ")
  random_part      <- paste(random_terms,      collapse = " + ")
  fmla             <- as.formula(paste0(dv, " ~ ",
                                        fixed_part, " + ",
                                        interaction_part, " + ",
                                        random_part))
  
  cat("\n[Step 2] Interactions model (continuous DV):\n ")
  cat(deparse(fmla), "\n")
  
  # progress print 
  cat("\nFitting model. The numbers below are the optimiser working -- R is fine, don't stress \n",
      "Started ", format(Sys.time(), "%H:%M:%S"), "\n", sep = "")
  utils::flush.console()
  started <- Sys.time()
  
  model <- lmerTest::lmer(fmla, data = data, REML = REML, control = control,
                          verbose = if (progress) 1L else 0L, ...)
  
  elapsed <- as.numeric(difftime(Sys.time(), started, units = "secs"))
  cat(sprintf("\nDone in %s\n",
              if (elapsed < 60) sprintf("%.0f seconds", elapsed)
              else sprintf("%.1f minutes", elapsed / 60)))
  
  cat("\n--- Summary ---\n")
  print(summary(model))
  invisible(model)
}

## compare models 
# this will compute the Likelihood Ratio Test between two models 
compare_models <- function(model_step1, model_step2) {
  cat("\n--- Model comparison (LRT) ---\n")
  comp <- anova(model_step1, model_step2)
  print(comp)
  invisible(comp)
}


## extracting coefficients from the model - categorical DV version
apa_fixed_effects_table <- function(model,
                                    title = "Fixed Effects",
                                    note  = "OR = odds ratio. CIs are 95% Wald intervals.") {
  data <- .make_fixed_effects_data(model) %>%
    rename(
      Predictor  = term,
      `b`        = estimate,
      `SE`       = se,
      `Wald χ²`  = Wald_ChiSq,
      `p`        = p,
      `OR`       = OR,
      `95% CI LL`= OR_lower,
      `95% CI UL`= OR_upper
    )
  
  ft <- .apa_flextable(data, title = title, note = note)
  print(ft)
  invisible(ft)
}

## extracting coefficients from the model - continuous DV version
apa_fixed_effects_table_lmer <- function(model,
                                         title = "Fixed Effects",
                                         note  = "CIs are 95% Wald intervals.") {
  data <- .make_fixed_effects_data_lmer(model) %>%
    rename(
      Predictor  = term,
      `b`        = estimate,
      `SE`       = se,
      `df`       = df,
      `t`        = t_value,
      `p`        = p,
      `95% CI LL`= CI_lower,
      `95% CI UL`= CI_upper
    )
  
  ft <- .apa_flextable(data, title = title, note = note)
  print(ft)
  invisible(ft)
}

## extracting simple slopes to clarify our interaction - categorical DV version
get_simple_effects_flex <- function(focal,
                                    moderator,
                                    raw_mod_col,
                                    mod_values,
                                    model,
                                    data,
                                    title = "Simple Effects") {
  b <- fixef(model)
  V <- vcov(model)
  
  # Find interaction term (R may flip the order)
  int_name <- intersect(
    c(paste0(focal, ":", moderator), paste0(moderator, ":", focal)),
    names(b)
  )
  if (length(int_name) == 0) stop("Interaction term not found in model.")
  int_name <- int_name[1]
  
  # Raw-to-z conversion for the moderator
  same_col <- identical(moderator, raw_mod_col)
  if (!same_col) {
    z_conv <- lm(as.formula(paste(moderator, "~", raw_mod_col)), data = data)
  }
  
  compute_one <- function(mod_value) {
    z_value  <- if (same_col) mod_value else
      predict(z_conv, newdata = setNames(data.frame(mod_value), raw_mod_col))
    estimate <- b[focal] + b[int_name] * z_value
    se       <- sqrt(
      V[focal, focal] +
        z_value^2 * V[int_name, int_name] +
        2 * z_value * V[focal, int_name]
    )
    p_value <- 2 * pnorm(abs(estimate / se), lower.tail = FALSE)
    data.frame(
      raw_moderator  = mod_value,
      z_moderator    = z_value,
      b              = estimate,
      SE             = se,
      Wald_ChiSq     = (estimate / se)^2,
      p              = p_value,
      OR             = exp(estimate),
      OR_lower       = exp(estimate - 1.96 * se),
      OR_upper       = exp(estimate + 1.96 * se),
      significant    = p_value < .05
    )
  }
  
  results <- bind_rows(lapply(mod_values, compute_one)) %>%
    mutate(p_fmt = ifelse(p < .001, "< .001", sub("^0", "", sprintf("%.3f", p)))) %>%
    mutate(across(where(is.numeric), ~ round(.x, 2))) %>%
    mutate(p = p_fmt) %>%
    select(-p_fmt)
  
  cat("\n--- Simple effects output ---\n")
  print(results, row.names = FALSE)
  
  # APA table (drop the significant flag column)
  table_data <- results %>%
    select(-significant) %>%
    rename(
      !!raw_mod_col  := raw_moderator,
      `z (moderator)`  = z_moderator,
      `Wald χ²`        = Wald_ChiSq,
      `OR`             = OR,
      `95% CI LL`      = OR_lower,
      `95% CI UL`      = OR_upper
    )
  
  note <- paste0(
    "Simple effects of ", focal, " at each level of ", raw_mod_col, ". ",
    "OR = odds ratio. CIs are 95% Wald intervals. ",
    "Significance threshold p < .05."
  )
  
  ft <- .apa_flextable(table_data, title = title, note = note)
  print(ft)
  invisible(list(results = results, table = ft))
}

## extracting simple slopes to clarify an interaction - continuous DV version
# same logic as get_simple_effects_flex() but reports raw b/CI instead of OR
get_simple_effects_flex_lmer <- function(focal,
                                         moderator,
                                         raw_mod_col,
                                         mod_values,
                                         model,
                                         data,
                                         title = "Simple Effects") {
  b <- fixef(model)
  V <- vcov(model)
  
  int_name <- intersect(
    c(paste0(focal, ":", moderator), paste0(moderator, ":", focal)),
    names(b)
  )
  if (length(int_name) == 0) stop("Interaction term not found in model.")
  int_name <- int_name[1]
  
  same_col <- identical(moderator, raw_mod_col)
  if (!same_col) {
    z_conv <- lm(as.formula(paste(moderator, "~", raw_mod_col)), data = data)
  }
  
  compute_one <- function(mod_value) {
    z_value  <- if (same_col) mod_value else
      predict(z_conv, newdata = setNames(data.frame(mod_value), raw_mod_col))
    estimate <- b[focal] + b[int_name] * z_value
    se       <- sqrt(
      V[focal, focal] +
        z_value^2 * V[int_name, int_name] +
        2 * z_value * V[focal, int_name]
    )
    p_value <- 2 * pnorm(abs(estimate / se), lower.tail = FALSE)
    data.frame(
      raw_moderator = mod_value,
      z_moderator   = z_value,
      b             = estimate,
      SE            = se,
      p             = p_value,
      CI_lower      = estimate - 1.96 * se,
      CI_upper      = estimate + 1.96 * se,
      significant   = p_value < .05
    )
  }
  
  results <- bind_rows(lapply(mod_values, compute_one)) %>%
    mutate(p_fmt = ifelse(p < .001, "< .001", sub("^0", "", sprintf("%.3f", p)))) %>%
    mutate(across(where(is.numeric), ~ round(.x, 2))) %>%
    mutate(p = p_fmt) %>%
    select(-p_fmt)
  
  cat("\n--- Simple effects output ---\n")
  print(results, row.names = FALSE)
  
  table_data <- results %>%
    select(-significant) %>%
    rename(
      !!raw_mod_col  := raw_moderator,
      `z (moderator)`  = z_moderator,
      `95% CI LL`      = CI_lower,
      `95% CI UL`      = CI_upper
    )
  
  note <- paste0(
    "Simple effects of ", focal, " at each level of ", raw_mod_col, ". ",
    "CIs are 95% Wald intervals. Significance threshold p < .05."
  )
  
  ft <- .apa_flextable(table_data, title = title, note = note)
  print(ft)
  invisible(list(results = results, table = ft))
}

## interaction plot function - categorical DV version
plot_interaction <- function(focal, moderator, raw_mod_col, main_fx, model, data, DV) {
  focal_range <- seq(min(data[[focal]], na.rm = TRUE),
                     max(data[[focal]], na.rm = TRUE),
                     length.out = 200)
  mod_levels <- sort(unique(data[[raw_mod_col]]))
  pred_grid  <- expand.grid(focal_vals = focal_range,
                            mod_vals   = mod_levels)
  names(pred_grid) <- c(focal, raw_mod_col)
  if (!identical(moderator, raw_mod_col)) {
    z_conv <- lm(as.formula(paste(moderator, "~", raw_mod_col)), data = data)
    pred_grid[[moderator]] <- predict(z_conv, newdata = pred_grid)
  }
  other_fx <- setdiff(main_fx, c(focal, moderator))
  for (v in other_fx) pred_grid[[v]] <- 0
  pred_grid$predicted_prob <- predict(model, newdata = pred_grid,
                                      type = "response", re.form = NA)
  pred_grid$mod_label <- factor(pred_grid[[raw_mod_col]])
  ggplot(pred_grid, aes(x = .data[[focal]], y = predicted_prob, colour = mod_label)) +
    geom_line(linewidth = 0.9) +
    scale_y_continuous(name = paste("Predicted P(", DV, ")"), limits = c(0, 1)) +
    labs(title  = paste("Interaction:", focal, "\u00d7", raw_mod_col),
         x      = focal, colour = raw_mod_col) +
    theme_classic(base_size = 13)
}


## values of the moderator to compute simple effects at
##   "levels" -- every observed level (for 0/1 or a few categories)
##   "sd"     -- mean and +/- 1 SD (the classic approach for continuous moderators)
get_mod_values <- function(data, raw_mod_col, method = c("levels", "sd")) {
  method <- match.arg(method)
  x <- data[[raw_mod_col]]
  
  if (method == "levels") {
    vals <- sort(unique(x[!is.na(x)]))
    if (length(vals) > 10) {
      cat(sprintf("\nNote: '%s' has %d distinct values -- method = \"sd\" is usually a better fit for a continuous moderator.\n",
                  raw_mod_col, length(vals)))
    }
  } else {
    m <- mean(x, na.rm = TRUE); s <- sd(x, na.rm = TRUE)
    vals <- c(m - s, m, m + s)
  }
  
  cat(sprintf("\nModerator values for %s: %s\n",
              raw_mod_col, paste(round(vals, 3), collapse = ", ")))
  vals
}


## simple effects + interaction plot, for either kind of model
## works out from the model itself whether to report odds ratios or raw b values
follow_up_interaction <- function(focal, moderator, raw_mod_col, mod_values,
                                  main_fx, model, data, DV, title = NULL) {
  is_glmer <- inherits(model, "glmerMod")
  
  if (is.null(title)) {
    title <- paste("Table 3. Simple Effects of", focal, "at Each Level of", raw_mod_col)
  }
  
  cat(sprintf("\nThis is a %s model, so the table below reports %s.\n",
              if (is_glmer) "categorical (glmer)" else "continuous (lmer)",
              if (is_glmer) "odds ratios" else "raw b values"))
  
  se_fun   <- if (is_glmer) get_simple_effects_flex else get_simple_effects_flex_lmer
  plot_fun <- if (is_glmer) plot_interaction        else plot_interaction_lmer
  
  se_output <- se_fun(focal = focal, moderator = moderator, raw_mod_col = raw_mod_col,
                      mod_values = mod_values, model = model, data = data, title = title)
  
  p <- plot_fun(focal, moderator, raw_mod_col, main_fx, model, data, DV)
  print(p)
  
  invisible(c(se_output, list(plot = p)))
}

# this will give us the Johnson-Neyman follow ups to an interaction - works for both DV types
get_jn <- function(focal, moderator, raw_mod_col, model, data,
                   p_threshold = .05, n_points = 1000,
                   effect_scale = NULL) {
  
  # y-axis label depends on the model type
  if (is.null(effect_scale)) {
    effect_scale <- if (inherits(model, "glmerMod")) "log-odds" else "raw units"
  }
  
  b <- fixef(model)
  V <- vcov(model)
  
  # Find interaction term (handles both orderings)
  int_name <- intersect(
    c(paste0(focal, ":", moderator), paste0(moderator, ":", focal)),
    names(b)
  )
  if (length(int_name) == 0) stop("Interaction term not found in model.")
  int_name <- int_name[1]
  
  # Raw-to-z conversion for the moderator
  same_col <- identical(moderator, raw_mod_col)
  if (!same_col) {
    z_conv <- lm(as.formula(paste(moderator, "~", raw_mod_col)), data = data)
  }
  
  compute_one <- function(mod_value) {
    z_value  <- if (same_col) mod_value else
      predict(z_conv, newdata = setNames(data.frame(mod_value), raw_mod_col))
    estimate <- b[focal] + b[int_name] * z_value
    se       <- sqrt(
      V[focal, focal] +
        z_value^2 * V[int_name, int_name] +
        2 * z_value * V[focal, int_name]
    )
    p_value <- 2 * pnorm(abs(estimate / se), lower.tail = FALSE)
    data.frame(
      raw_moderator      = mod_value,
      z_moderator        = z_value,
      simple_slope       = estimate,
      simple_slope_lower = estimate - 1.96 * se,
      simple_slope_upper = estimate + 1.96 * se,
      p                  = p_value
    )
  }
  
  # Full curve across observed moderator range
  mod_min      <- min(data[[raw_mod_col]], na.rm = TRUE)
  mod_max      <- max(data[[raw_mod_col]], na.rm = TRUE)
  search_vals  <- seq(mod_min, mod_max, length.out = n_points)
  jn_data      <- bind_rows(lapply(search_vals, compute_one))
  
  # label contiguous runs so a split significant region isn't drawn as one shape
  jn_data$sig    <- jn_data$p < p_threshold
  jn_data$region <- cumsum(c(1, abs(diff(jn_data$sig))))
  
  # Find exact JN transition point(s) via root finding
  p_minus_threshold  <- function(x) compute_one(x)$p - p_threshold
  p_vals             <- sapply(search_vals, p_minus_threshold)
  crossing_indices   <- which(diff(sign(p_vals)) != 0)
  
  jn_points <- if (length(crossing_indices) == 0) numeric(0) else
    vapply(crossing_indices, function(i) {
      uniroot(p_minus_threshold,
              lower = search_vals[i],
              upper = search_vals[i + 1])$root
    }, numeric(1))
  
  # Print and APA-table the transition point(s)
  if (length(jn_points) == 0) {
    cat("\nNo Johnson-Neyman transition point found in the observed range.\n")
    cat(sprintf("Effect is %s throughout.\n",
                if (all(jn_data$sig)) "significant" else "non-significant"))
  } else {
    jn_table <- bind_rows(lapply(jn_points, function(pt) {
      row <- compute_one(pt)
      data.frame(
        `Transition point` = round(pt, 4),
        `z (moderator)`    = round(row$z_moderator, 4),
        `b (focal)`        = round(row$simple_slope, 4),
        `p`                = round(row$p, 4),
        check.names        = FALSE
      )
    }))
    cat("\n--- Johnson-Neyman transition point(s) ---\n")
    
    ft <- .apa_flextable(
      jn_table,
      title = paste("Johnson-Neyman Transition Point(s):",
                    focal, "×", raw_mod_col),
      note  = paste0("Value(s) of ", raw_mod_col,
                     " where the simple effect of ", focal,
                     " crosses p = ", p_threshold,
                     ". Effects are significant outside this boundary.")
    )
    print(ft)
  }
  
  # Plot
  jn_plot <- ggplot(jn_data, aes(x = raw_moderator, y = simple_slope)) +
    
    # Shade significant region(s)
    geom_ribbon(
      data = filter(jn_data, sig),
      aes(ymin = simple_slope_lower, ymax = simple_slope_upper, group = region),
      fill = "#2C3E6B", alpha = 0.15
    ) +
    # Non-significant region
    geom_ribbon(
      data = filter(jn_data, !sig),
      aes(ymin = simple_slope_lower, ymax = simple_slope_upper, group = region),
      fill = "#AABDD4", alpha = 0.15
    ) +
    
    geom_line(linewidth = 0.9, colour = "#2C3E6B") +
    geom_hline(yintercept = 0, linetype = "dashed", colour = "grey50") +
    
    scale_x_continuous(name = raw_mod_col) +
    scale_y_continuous(name = paste("Simple effect of", focal, "\n(", effect_scale, ")")) +
    
    labs(
      title    = "Johnson-Neyman Plot",
      subtitle = paste("Region(s) of significance for", focal, "×", raw_mod_col)
    ) +
    
    theme_classic(base_size = 13) +
    theme(
      plot.title    = element_text(face = "bold", size = 14),
      plot.subtitle = element_text(colour = "grey40", size = 11),
      panel.grid.major.y = element_line(colour = "grey92", linewidth = 0.4)
    )
  
  # only add the JN markers if there's a transition point to mark
  if (length(jn_points) > 0) {
    jn_plot <- jn_plot +
      geom_vline(xintercept = jn_points, linetype = "dotted", colour = "#2C3E6B") +
      annotate("text",
               x      = jn_points,
               y      = max(jn_data$simple_slope_upper, na.rm = TRUE),
               label  = paste("JN =", round(jn_points, 3)),
               hjust  = -0.1,
               size   = 3.5,
               colour = "#2C3E6B")
  }
  
  print(jn_plot)
  
  invisible(list(
    jn_data   = jn_data,
    jn_points = jn_points,
    plot      = jn_plot
  ))
}

## interaction plot function - continuous DV version
# no type = "response"/logit transform needed - lmer predictions are already on the DV's own scale
plot_interaction_lmer <- function(focal, moderator, raw_mod_col, main_fx, model, data, DV) {
  focal_range <- seq(min(data[[focal]], na.rm = TRUE),
                     max(data[[focal]], na.rm = TRUE),
                     length.out = 200)
  mod_levels <- sort(unique(data[[raw_mod_col]]))
  pred_grid  <- expand.grid(focal_vals = focal_range,
                            mod_vals   = mod_levels)
  names(pred_grid) <- c(focal, raw_mod_col)
  if (!identical(moderator, raw_mod_col)) {
    z_conv <- lm(as.formula(paste(moderator, "~", raw_mod_col)), data = data)
    pred_grid[[moderator]] <- predict(z_conv, newdata = pred_grid)
  }
  other_fx <- setdiff(main_fx, c(focal, moderator))
  for (v in other_fx) pred_grid[[v]] <- 0
  pred_grid$predicted_DV <- predict(model, newdata = pred_grid, re.form = NA)
  pred_grid$mod_label <- factor(pred_grid[[raw_mod_col]])
  ggplot(pred_grid, aes(x = .data[[focal]], y = predicted_DV, colour = mod_label)) +
    geom_line(linewidth = 0.9) +
    scale_y_continuous(name = paste("Predicted", DV)) +
    labs(title  = paste("Interaction:", focal, "\u00d7", raw_mod_col),
         x      = focal, colour = raw_mod_col) +
    theme_classic(base_size = 13)
}


## save a table to word
save_apa_docx <- function(ft, filename = "table.docx") {
  read_docx() %>%
    body_add_flextable(ft) %>%
    print(target = filename)
  cat(sprintf("\nSaved: %s\n", filename))
}



## survey calculations
# reverse score 
reverse_code <- function(x, max_score, min_score = 1) {
  (max_score + min_score) - x
}
# score scale 
score_scale <- function(data, items, method = "mean", min_valid = 1) {
  item_data <- data[, items, drop = FALSE]
  n_valid <- rowSums(!is.na(item_data))
  
  if (method == "sum") {
    score <- rowSums(item_data, na.rm = TRUE)
  } else if (method == "mean") {
    score <- rowMeans(item_data, na.rm = TRUE)
  } else {
    stop("method must be 'sum' or 'mean'")
  }
  # could set score to NA if too few valid items were present
  score[n_valid < min_valid] <- NA
  score
}


## --- shared building blocks ------------------------------------------------

# default palette (matches the colours used in section 3)
.fig_default_colours <- c("#2C3E6B", "#C46B4E", "#5B8C6A", "#D4A843", "#8E6C8A",
                          "#4E8C9E", "#9E4E5B", "#AABDD4", "#6B6B6B")

# pick n colours, repeating (with a note) if too few were supplied
.fig_pick_colours <- function(colours, n) {
  if (is.null(colours)) colours <- .fig_default_colours
  if (length(colours) < n) {
    cat(sprintf("\nNote: %d colour(s) supplied but %d needed - colours will repeat. Add more to colours = c(...).\n",
                length(colours), n))
    colours <- rep_len(colours, n)
  }
  unname(colours[seq_len(n)])
}

# tick marks from a range and an interval size
.fig_breaks <- function(limits, by) {
  if (is.null(by)) return(ggplot2::waiver())
  if (!is.null(limits)) return(seq(limits[1], limits[2], by = by))
  function(lims) seq(floor(lims[1] / by) * by, ceiling(lims[2] / by) * by, by = by)
}

# shared APA-ish theme, including where the key goes
.fig_theme <- function(base_size = 13, legend_position = "right",
                       legend_inside = c(0.02, 0.98), legend_box = TRUE,
                       title_size = NULL, subtitle_size = NULL,
                       axis_title_size = NULL, axis_text_size = NULL,
                       legend_title_size = NULL, legend_text_size = NULL,
                       panel_title_size = NULL) {
  # NULL text sizes are worked out from base_size, so setting base_size alone still scales everything
  if (is.null(title_size))        title_size        <- base_size + 1
  if (is.null(subtitle_size))     subtitle_size     <- base_size - 2
  if (is.null(axis_title_size))   axis_title_size   <- base_size
  if (is.null(axis_text_size))    axis_text_size    <- base_size - 2
  if (is.null(legend_title_size)) legend_title_size <- base_size - 1
  if (is.null(legend_text_size))  legend_text_size  <- base_size - 2
  if (is.null(panel_title_size))  panel_title_size  <- base_size - 1
  
  th <- theme_classic(base_size = base_size) +
    theme(plot.title       = element_text(face = "bold", hjust = 0.5, size = title_size),
          plot.subtitle    = element_text(hjust = 0.5, size = subtitle_size, colour = "grey40"),
          axis.title       = element_text(size = axis_title_size),
          axis.text        = element_text(size = axis_text_size),
          legend.title     = element_text(size = legend_title_size),
          legend.text      = element_text(size = legend_text_size),
          strip.background = element_blank(),
          strip.text       = element_text(face = "bold", size = panel_title_size),
          panel.spacing    = unit(1.4, "lines"))
  
  if (is.numeric(legend_position)) {            # c(x, y) given straight to legend_position also works
    legend_inside   <- legend_position
    legend_position <- "inside"
  }
  allowed <- c("right", "left", "top", "bottom", "none", "inside")
  if (!legend_position %in% allowed) {
    stop(sprintf("legend_position must be one of: %s", paste(allowed, collapse = ", ")))
  }
  
  if (legend_position == "inside") {
    if (!is.numeric(legend_inside) || length(legend_inside) != 2) {
      stop("legend_inside needs two numbers between 0 and 1, e.g. legend_inside = c(0.02, 0.98)")
    }
    # the key's own corner is anchored to the same spot, so c(1, 1) tucks it into the top-right without spilling over the edge
    th <- th + (if (utils::packageVersion("ggplot2") >= "3.5.0") {
      theme(legend.position = "inside", legend.position.inside = legend_inside,
            legend.justification = legend_inside)
    } else {
      theme(legend.position = legend_inside, legend.justification = legend_inside)
    })
    if (legend_box) {
      th <- th + theme(legend.background = element_rect(fill = "white", colour = "grey70", linewidth = 0.3),
                       legend.margin     = margin(4, 6, 4, 6))
    }
  } else {
    th <- th + theme(legend.position = legend_position)
  }
  th
}

# APA number formatting (no leading zero), e.g. 0.34 -> .34
.fig_apa_num <- function(x, digits = 2) {
  sub("^(-?)0\\.", "\\1.", formatC(x, format = "f", digits = digits))
}

# format level values for labels: whole numbers stay whole, others get decimals
.fig_fmt_levels <- function(values, digits = 2) {
  vn <- suppressWarnings(as.numeric(as.character(values)))
  if (any(is.na(vn))) return(as.character(values))
  if (all(abs(vn - round(vn)) < 1e-9)) return(as.character(round(vn)))
  formatC(vn, format = "f", digits = digits)
}

# does x equal a level? (numbers compared as numbers, everything else as trimmed text)
.fig_same_level <- function(x, level) {
  xn <- suppressWarnings(as.numeric(as.character(x)))
  ln <- suppressWarnings(as.numeric(as.character(level)))
  if (!is.na(ln) && !all(is.na(xn))) return(!is.na(xn) & abs(xn - ln) < 1e-6)
  !is.na(x) & trimws(as.character(x)) == trimws(as.character(level))
}

# which level (1, 2, 3...) each value of x belongs to (NA if none)
.fig_level_index <- function(x, levels) {
  idx <- rep(NA_integer_, length(x))
  for (i in seq_along(levels)) idx[is.na(idx) & .fig_same_level(x, levels[i])] <- i
  idx
}

# tidy up requested levels: snap nearly-right numbers to the closest real level, and warn about ones that don't exist
.fig_resolve_levels <- function(x, levels, var, tol = 0.005) {
  xn <- suppressWarnings(as.numeric(as.character(x)))
  ln <- suppressWarnings(as.numeric(as.character(levels)))
  if (!all(is.na(xn)) && !any(is.na(ln))) {
    obs <- sort(unique(xn[!is.na(xn)]))
    for (i in seq_along(ln)) {
      if (any(abs(obs - ln[i]) < 1e-6)) next
      j <- which.min(abs(obs - ln[i]))
      if (abs(obs[j] - ln[i]) <= tol) {
        cat(sprintf("\nNote: %s = %s was matched to the closest real level, %s.\n", var, ln[i], signif(obs[j], 6)))
        ln[i] <- obs[j]
      }
    }
    levels <- ln
  }
  found <- vapply(levels, function(l) any(.fig_same_level(x, l)), logical(1))
  if (any(!found)) {
    avail <- sort(unique(x[!is.na(x)]))
    shown <- paste(head(avail, 20), collapse = ", ")
    if (length(avail) > 20) shown <- paste0(shown, ", ... (", length(avail), " levels in total)")
    cat(sprintf("\nWarning: level(s) %s not found in '%s'. Available levels are: %s\n",
                paste(levels[!found], collapse = ", "), var, shown))
  }
  levels
}

.fig_check_cols <- function(data, cols) {
  missing <- setdiff(cols, names(data))
  if (length(missing) > 0) stop(sprintf("Column(s) not found in the data: %s", paste(missing, collapse = ", ")))
}

# keep only the rows matching include = list(variable = levels, ...)
.fig_apply_include <- function(data, include) {
  if (is.null(include) || length(include) == 0) return(data)
  if (!is.list(include) || is.null(names(include)) || any(names(include) == "")) {
    stop("include needs to be a named list, e.g. include = list(task_name = \"feedback\", stepIndex = 2:9)")
  }
  .fig_check_cols(data, names(include))
  n_before <- nrow(data)
  for (v in names(include)) {
    include[[v]] <- .fig_resolve_levels(data[[v]], include[[v]], v)
    data <- data[!is.na(.fig_level_index(data[[v]], include[[v]])), , drop = FALSE]
  }
  cat(sprintf("\nIncluded only %s: %d of %d rows kept.\n",
              paste(sprintf("%s = %s", names(include),
                            vapply(include, function(l) paste(l, collapse = ", "), character(1))), collapse = "; "),
              nrow(data), n_before))
  if (nrow(data) == 0) stop("No rows left after include - check the variable names and levels.")
  attr(data, "include") <- include
  data
}

# report how much of the data sits inside the x-axis range
.fig_range_note <- function(x, limits, name) {
  if (is.null(limits)) return(invisible(NULL))
  inside <- mean(x >= limits[1] & x <= limits[2], na.rm = TRUE)
  cat(sprintf("\n%.1f%% of '%s' values fall inside the x-axis range (%s to %s).\n",
              100 * inside, name, limits[1], limits[2]))
}

## --- model prediction engine (used by 5.1 and 5.5) --------------------------

.fig_is_glmer <- function(model) inherits(model, "glmerMod")
.fig_dv_name  <- function(model) names(model.frame(model))[1]

# raw moderator values -> the z-scored values used in the model (same approach as follow_up_interaction)
.fig_raw_to_z <- function(values, moderator, raw_mod_col, data) {
  if (identical(moderator, raw_mod_col)) return(unname(values))
  z_conv <- lm(as.formula(paste(moderator, "~", raw_mod_col)), data = data)
  unname(predict(z_conv, newdata = setNames(data.frame(unname(values)), raw_mod_col)))
}

# single levels given in include become the values other model predictors are held at
.fig_hold_from_include <- function(data, model, exclude) {
  inc <- attr(data, "include")
  if (is.null(inc)) return(NULL)
  preds <- all.vars(delete.response(terms(model, fixed.only = TRUE)))
  inc   <- inc[names(inc) %in% setdiff(preds, exclude) & lengths(inc) == 1]
  if (length(inc) > 0) {
    cat(sprintf("\nPredictions hold %s (from include).\n",
                paste(sprintf("%s at %s", names(inc), unlist(inc)), collapse = ", ")))
  }
  inc
}

# fixed-effect predictions with confidence intervals (random effects at their average)
.fig_predict <- function(model, newdata, hold_at = "zero", hold_values = NULL, conf_level = 0.95) {
  tt     <- delete.response(terms(model, fixed.only = TRUE))
  mf     <- model.frame(model)
  needed <- all.vars(tt)
  
  # any predictor not being plotted is held constant
  for (v in setdiff(needed, names(newdata))) {
    col <- mf[[v]]
    if (is.null(col)) stop(sprintf("Couldn't find '%s' in the model's data.", v))
    if (!is.null(hold_values) && v %in% names(hold_values)) {
      newdata[[v]] <- if (is.numeric(col)) as.numeric(hold_values[[v]]) else as.character(hold_values[[v]])
    } else if (is.numeric(col) || is.logical(col)) {
      newdata[[v]] <- if (hold_at == "mean") mean(as.numeric(col), na.rm = TRUE) else 0
    } else {
      newdata[[v]] <- levels(factor(col))[1]
    }
  }
  
  cat_vars <- needed[needed %in% names(mf)]
  cat_vars <- cat_vars[vapply(cat_vars, function(v) is.factor(mf[[v]]) || is.character(mf[[v]]), logical(1))]
  xlev     <- lapply(setNames(cat_vars, cat_vars), function(v) levels(factor(mf[[v]])))
  
  mf_new <- model.frame(tt, newdata, xlev = if (length(xlev)) xlev else NULL, na.action = na.pass)
  X      <- model.matrix(tt, mf_new)
  b      <- lme4::fixef(model)
  if (!all(names(b) %in% colnames(X))) stop("Couldn't rebuild the model's predictors for plotting - check the model runs without warnings.")
  X      <- X[, names(b), drop = FALSE]
  V      <- as.matrix(vcov(model))
  
  eta  <- as.vector(X %*% b)
  se   <- sqrt(rowSums((X %*% V) * X))
  crit <- qnorm(1 - (1 - conf_level) / 2)
  inv  <- if (.fig_is_glmer(model)) family(model)$linkinv else identity
  
  newdata$fit   <- inv(eta)
  newdata$lower <- inv(eta - crit * se)
  newdata$upper <- inv(eta + crit * se)
  newdata
}

# automatic labels for moderator values (-1 SD / Mean / +1 SD, or the values themselves)
.fig_mod_labels <- function(values, raw_mod_col, data, digits = 2) {
  values <- unname(values)
  x <- data[[raw_mod_col]]
  m <- mean(x, na.rm = TRUE); s <- sd(x, na.rm = TRUE)
  if (length(values) == 3 && isTRUE(all.equal(values, c(m - s, m, m + s), tolerance = 1e-6))) {
    return(c(sprintf("-1 SD (%s)", formatC(m - s, format = "f", digits = digits)),
             sprintf("Mean (%s)",  formatC(m,     format = "f", digits = digits)),
             sprintf("+1 SD (%s)", formatC(m + s, format = "f", digits = digits))))
  }
  .fig_fmt_levels(values, digits)
}


## --- 5.1 interaction lines (logistic OR linear) -----------------------------
plot_interaction_lines <- function(model, data, focal, moderator, raw_mod_col, mod_values,
                                   mod_labels      = NULL,
                                   include         = list(),
                                   x_limits        = c(-2, 2),  x_by = 1,
                                   y_limits        = NULL,      y_by = NULL,
                                   focal_values    = NULL,      focal_labels = NULL,
                                   x_label         = focal,     y_label = NULL,
                                   legend_title    = raw_mod_col,
                                   title           = NULL,
                                   colours         = NULL,      linetypes = NULL,
                                   show_ci         = TRUE,      ci_alpha = 0.15,
                                   line_width      = 1,
                                   hold_at         = "zero",    conf_level = 0.95,
                                   legend_position = "right",   legend_inside = c(0.02, 0.98),
                                   legend_box      = TRUE,
                                   title_size      = NULL, subtitle_size    = NULL,
                                   axis_title_size = NULL, axis_text_size   = NULL,
                                   legend_title_size = NULL, legend_text_size = NULL,
                                   base_size = 13) {
  data <- .fig_apply_include(as.data.frame(data), include)
  .fig_check_cols(data, c(focal, moderator, raw_mod_col))
  dv       <- .fig_dv_name(model)
  is_glmer <- .fig_is_glmer(model)
  discrete <- !is.null(focal_values)
  holds    <- .fig_hold_from_include(data, model, exclude = c(focal, moderator))
  
  if (is.null(y_label))  y_label  <- if (is_glmer) paste0("Predicted P(", dv, ")") else paste("Predicted", dv)
  if (is.null(y_limits) && is_glmer) y_limits <- c(0, 1)
  if (is.null(x_limits) && !discrete) x_limits <- range(data[[focal]], na.rm = TRUE)
  if (is.null(mod_labels)) mod_labels <- .fig_mod_labels(mod_values, raw_mod_col, data)
  if (length(mod_labels) != length(mod_values)) stop("mod_labels needs one label per value in mod_values.")
  if (discrete && is.null(focal_labels)) focal_labels <- .fig_fmt_levels(focal_values)
  
  z_mod  <- .fig_raw_to_z(mod_values, moderator, raw_mod_col, data)
  f_vals <- if (discrete) focal_values else seq(x_limits[1], x_limits[2], length.out = 200)
  
  grid <- expand.grid(.f = f_vals, .k = seq_along(mod_values))
  grid[[focal]]     <- grid$.f
  grid[[moderator]] <- z_mod[grid$.k]
  grid$mod_label    <- factor(mod_labels[grid$.k], levels = mod_labels)
  pred <- .fig_predict(model, grid, hold_at = hold_at, hold_values = holds, conf_level = conf_level)
  
  if (!discrete) .fig_range_note(data[[focal]], x_limits, focal)
  cat(sprintf("\nPlotting a %s model: y is %s.\n",
              if (is_glmer) "categorical (glmer)" else "continuous (lmer)",
              if (is_glmer) "a predicted probability" else "the predicted DV in its own units"))
  
  n    <- length(mod_values)
  cols <- .fig_pick_colours(colours, n)
  lts  <- if (is.null(linetypes)) rep("solid", n) else rep_len(linetypes, n)
  
  if (!discrete) {
    p <- ggplot(pred, aes(x = .f, y = fit, colour = mod_label, fill = mod_label, linetype = mod_label))
    if (show_ci) p <- p + geom_ribbon(aes(ymin = lower, ymax = upper), alpha = ci_alpha, colour = NA)
    p <- p + geom_line(linewidth = line_width) +
      scale_x_continuous(name = x_label, breaks = .fig_breaks(x_limits, x_by))
  } else {
    pred$.f_lab <- factor(focal_labels[match(pred$.f, focal_values)], levels = focal_labels)
    pd <- position_dodge(width = 0.35)
    p  <- ggplot(pred, aes(x = .f_lab, y = fit, colour = mod_label, linetype = mod_label, group = mod_label)) +
      geom_line(position = pd, linewidth = line_width * 0.7)
    if (show_ci) p <- p + geom_errorbar(aes(ymin = lower, ymax = upper), position = pd, width = 0.12, linetype = "solid")
    p <- p + geom_point(position = pd, size = 2.8) + labs(x = x_label)
  }
  
  p +
    scale_y_continuous(name = y_label, breaks = .fig_breaks(y_limits, y_by)) +
    scale_colour_manual(values = cols, name = legend_title) +
    scale_fill_manual(values = cols, name = legend_title) +
    scale_linetype_manual(values = lts, name = legend_title) +
    coord_cartesian(xlim = if (discrete) NULL else x_limits, ylim = y_limits) +
    labs(title = title) +
    .fig_theme(base_size, legend_position, legend_inside, legend_box,
               title_size, subtitle_size, axis_title_size, axis_text_size,
               legend_title_size, legend_text_size)
}


## --- 5.2 between-person scatterplot -----------------------------------------
plot_person_scatter <- function(data, x_var, dv, id_col = "subject",
                                include         = list(),
                                group_var       = NULL, group_levels = NULL, group_labels = NULL,
                                x_label         = x_var, y_label = NULL,
                                legend_title    = group_var, title = NULL,
                                x_limits        = NULL, x_by = NULL,
                                y_limits        = c(0, 1), y_by = 0.2,
                                colours         = NULL, shapes = c(16, 17, 15, 18),
                                point_size      = 2.2, point_alpha = 0.6, jitter_width = 0,
                                show_ci         = TRUE, ci_alpha = 0.15, conf_level = 0.95,
                                line_width      = 1, min_rows = 1,
                                legend_position = "right", legend_inside = c(0.02, 0.98),
                                legend_box      = TRUE,
                                title_size      = NULL, subtitle_size    = NULL,
                                axis_title_size = NULL, axis_text_size   = NULL,
                                legend_title_size = NULL, legend_text_size = NULL,
                                base_size       = 13) {
  data <- .fig_apply_include(as.data.frame(data), include)
  .fig_check_cols(data, c(x_var, dv, id_col, group_var))
  if (is.null(y_label)) y_label <- paste("Mean", dv, "per participant")
  
  has_group <- !is.null(group_var)
  if (has_group) {
    if (is.null(group_levels)) group_levels <- sort(unique(data[[group_var]][!is.na(data[[group_var]])]))
    group_levels <- .fig_resolve_levels(data[[group_var]], group_levels, group_var)
    if (is.null(group_labels)) group_labels <- .fig_fmt_levels(group_levels)
    data$.g_idx <- .fig_level_index(data[[group_var]], group_levels)
  } else {
    group_labels <- "all"
    data$.g_idx  <- 1L
  }
  
  data <- data[!is.na(data[[dv]]) & !is.na(data[[x_var]]) & !is.na(data$.g_idx), , drop = FALSE]
  
  pp <- data %>%
    group_by(.id = .data[[id_col]], .g_idx) %>%
    summarise(x      = mean(.data[[x_var]]),
              x_vals = n_distinct(.data[[x_var]]),
              y      = mean(.data[[dv]]),
              n_rows = n(), .groups = "drop") %>%
    filter(n_rows >= min_rows)
  
  if (any(pp$x_vals > 1)) {
    cat(sprintf("\nWarning: '%s' changes within %d participant(s) - their average was used. Is it really a between-person variable?\n",
                x_var, sum(pp$x_vals > 1)))
  }
  pp$.g_lab <- factor(group_labels[pp$.g_idx], levels = group_labels)
  
  cat("\n--- Participant-level correlations ---\n")
  for (g in levels(pp$.g_lab)) {
    sub <- pp[pp$.g_lab == g, ]
    if (nrow(sub) >= 4) {
      ct <- cor.test(sub$x, sub$y)
      cat(sprintf("%s: r(%d) = %s, p %s, N = %d\n", g, ct$parameter, .fig_apa_num(ct$estimate),
                  ifelse(ct$p.value < .001, "< .001", paste("=", .fig_apa_num(ct$p.value, 3))), nrow(sub)))
    } else {
      cat(sprintf("%s: too few participants (N = %d) for a correlation\n", g, nrow(sub)))
    }
  }
  
  n    <- length(group_labels)
  cols <- .fig_pick_colours(colours, n)
  shp  <- rep_len(shapes, n)
  
  p <- ggplot(pp, aes(x = x, y = y, colour = .g_lab, fill = .g_lab, shape = .g_lab)) +
    geom_point(size = point_size, alpha = point_alpha,
               position = position_jitter(width = jitter_width, height = 0, seed = 1)) +
    geom_smooth(method = "lm", formula = y ~ x, se = show_ci, level = conf_level,
                alpha = ci_alpha, linewidth = line_width) +
    scale_colour_manual(values = cols, name = legend_title) +
    scale_fill_manual(values = cols,   name = legend_title) +
    scale_shape_manual(values = shp,   name = legend_title) +
    scale_x_continuous(name = x_label, breaks = .fig_breaks(x_limits, x_by)) +
    scale_y_continuous(name = y_label, breaks = .fig_breaks(y_limits, y_by)) +
    coord_cartesian(xlim = x_limits, ylim = y_limits) +
    labs(title = title) +
    .fig_theme(base_size, legend_position, legend_inside, legend_box,
               title_size, subtitle_size, axis_title_size, axis_text_size,
               legend_title_size, legend_text_size)
  
  if (!has_group) p <- p + guides(colour = "none", fill = "none", shape = "none")
  p
}


## --- 5.3 Johnson-Neyman plot (tidy, editable version of get_jn's plot) -----
plot_jn <- function(jn_output,
                    x_label         = "Moderator", y_label = NULL,
                    title           = "Johnson-Neyman Plot", subtitle = NULL,
                    odds_ratio      = FALSE,      show_ci = TRUE,
                    x_limits        = NULL, x_by = NULL,
                    y_limits        = NULL, y_by = NULL,
                    line_colour     = "#2C3E6B",
                    sig_colour      = "#2C3E6B", nonsig_colour = "#AABDD4",
                    sig_label       = "p < .05",  nonsig_label  = "n.s.",
                    legend_title    = NULL,       ribbon_alpha  = 0.25,
                    show_jn_lines   = TRUE,       jn_digits     = 2,
                    grid_y          = TRUE,
                    jn_label_prefix = "JN = ",    jn_label_size = 3.5,
                    line_width      = 0.9,
                    legend_position = "none",     legend_inside = c(0.02, 0.98),
                    legend_box      = TRUE,
                    title_size      = NULL, subtitle_size     = NULL,
                    axis_title_size = NULL, axis_text_size    = NULL,
                    legend_title_size = NULL, legend_text_size = NULL,
                    base_size       = 13) {
  jd  <- as.data.frame(jn_output$jn_data)
  pts <- jn_output$jn_points
  
  tr <- if (odds_ratio) exp else identity
  jd$est <- tr(jd$simple_slope)
  jd$lo  <- tr(jd$simple_slope_lower)
  jd$hi  <- tr(jd$simple_slope_upper)
  jd$sig_lab <- factor(ifelse(jd$sig, sig_label, nonsig_label), levels = c(sig_label, nonsig_label))
  if (is.null(y_label)) y_label <- if (odds_ratio) "Simple effect (odds ratio)" else "Simple effect (b)"
  
  if (length(pts) == 0) {
    cat("\nNote: no Johnson-Neyman point in the observed range - the effect doesn't cross the threshold, so the whole line is one region.\n")
  }
  
  # ribbons: each region borrows one point from the next so there's no gap at the JN point
  rib <- do.call(rbind, lapply(unique(jd$region), function(r) {
    idx <- which(jd$region == r)
    nxt <- max(idx) + 1
    if (nxt <= nrow(jd)) {
      extra <- jd[nxt, ]; extra$region <- r; extra$sig_lab <- jd$sig_lab[idx[1]]
      rbind(jd[idx, ], extra)
    } else jd[idx, ]
  }))
  
  p <- ggplot(jd, aes(x = raw_moderator, y = est))
  if (show_ci) {                                   # shaded 95% CI, darker where p < .05
    p <- p + geom_ribbon(data = rib, aes(ymin = lo, ymax = hi, fill = sig_lab, group = region),
                         alpha = ribbon_alpha)
  }
  p <- p +
    geom_hline(yintercept = if (odds_ratio) 1 else 0, linetype = "dashed", colour = "grey50") +
    geom_line(colour = line_colour, linewidth = line_width) +
    scale_fill_manual(values = setNames(c(sig_colour, nonsig_colour), c(sig_label, nonsig_label)),
                      name = legend_title, drop = FALSE)
  
  if (show_jn_lines && length(pts) > 0) {
    y_top <- if (!is.null(y_limits)) y_limits[2] else max(if (show_ci) jd$hi else jd$est, na.rm = TRUE)
    p <- p +
      geom_vline(xintercept = pts, linetype = "dotted", colour = line_colour) +
      annotate("text", x = pts, y = y_top,
               label = paste0(jn_label_prefix, formatC(pts, format = "f", digits = jn_digits)),
               hjust = if (length(pts) == 1) -0.08 else ifelse(seq_along(pts) == 1, 1.08, -0.08),
               vjust = 1, size = jn_label_size, colour = line_colour)
  }
  
  p <- p +
    scale_x_continuous(name = x_label, breaks = .fig_breaks(x_limits, x_by)) +
    scale_y_continuous(name = y_label, breaks = .fig_breaks(y_limits, y_by)) +
    coord_cartesian(xlim = x_limits, ylim = y_limits) +
    labs(title = title, subtitle = subtitle) +
    .fig_theme(base_size, legend_position, legend_inside, legend_box,
               title_size, subtitle_size, axis_title_size, axis_text_size,
               legend_title_size, legend_text_size)
  if (grid_y) p <- p + theme(panel.grid.major.y = element_line(colour = "grey92", linewidth = 0.4))
  p
}


## --- 5.4 box-and-whisker with one dot per participant ------------------------
plot_person_boxplot <- function(data, x_var, dv, id_col = "subject",
                                include         = list(),
                                x_levels        = NULL, x_labels = NULL,
                                split_var       = NULL, split_levels = NULL, split_labels = NULL,
                                split_style     = "dodge",
                                x_label         = x_var, y_label = NULL,
                                legend_title    = split_var, title = NULL,
                                y_limits        = c(0, 1), y_by = 0.2,
                                colours         = NULL,
                                box_width       = 0.5, box_alpha = 0.3,
                                point_size      = 1.8, point_alpha = 0.6, jitter_width = 0.06,
                                connect_lines   = NULL, line_alpha = 0.2,
                                show_mean       = TRUE, dodge_width = 0.6,
                                legend_position = "right", legend_inside = c(0.02, 0.98),
                                legend_box      = TRUE,
                                title_size      = NULL, subtitle_size    = NULL,
                                axis_title_size = NULL, axis_text_size   = NULL,
                                legend_title_size = NULL, legend_text_size = NULL,
                                panel_title_size  = NULL,
                                base_size       = 13, seed = 1) {
  data <- .fig_apply_include(as.data.frame(data), include)
  .fig_check_cols(data, c(x_var, dv, id_col, split_var))
  if (is.null(y_label)) y_label <- paste("Mean", dv, "per participant")
  
  if (is.null(x_levels)) x_levels <- sort(unique(data[[x_var]][!is.na(data[[x_var]])]))
  x_levels <- .fig_resolve_levels(data[[x_var]], x_levels, x_var)
  if (is.null(x_labels)) x_labels <- .fig_fmt_levels(x_levels)
  if (length(x_labels) != length(x_levels)) stop("x_labels needs one label per level in x_levels.")
  data$.x_idx <- .fig_level_index(data[[x_var]], x_levels)
  
  has_split <- !is.null(split_var)
  if (has_split) {
    if (is.null(split_levels)) split_levels <- sort(unique(data[[split_var]][!is.na(data[[split_var]])]))
    split_levels <- .fig_resolve_levels(data[[split_var]], split_levels, split_var)
    if (is.null(split_labels)) split_labels <- .fig_fmt_levels(split_levels)
    if (length(split_labels) != length(split_levels)) stop("split_labels needs one label per level in split_levels.")
    data$.s_idx <- .fig_level_index(data[[split_var]], split_levels)
  } else {
    split_labels <- "all"
    data$.s_idx  <- 1L
  }
  dodge <- has_split && split_style == "dodge"
  if (is.null(connect_lines)) connect_lines <- !dodge   # lines get messy when boxes are side by side
  
  data <- data[!is.na(data$.x_idx) & !is.na(data$.s_idx) & !is.na(data[[dv]]), , drop = FALSE]
  if (nrow(data) == 0) stop("No rows to plot - check x_levels / split_levels / include.")
  
  pp <- data %>%
    group_by(.id = .data[[id_col]], .x_idx, .s_idx) %>%
    summarise(y = mean(.data[[dv]]), n_rows = n(), .groups = "drop")
  
  n_x <- length(x_levels); n_s <- length(split_labels)
  offset       <- if (dodge) (pp$.s_idx - (n_s + 1) / 2) * (dodge_width / n_s) else 0
  pp$.pos      <- pp$.x_idx + offset
  set.seed(seed)
  pp$.pos_j    <- pp$.pos + runif(nrow(pp), -jitter_width, jitter_width)
  pp$.x_lab    <- factor(x_labels[pp$.x_idx],     levels = x_labels)
  pp$.s_lab    <- factor(split_labels[pp$.s_idx], levels = split_labels)
  pp$.col      <- if (dodge) pp$.s_lab else pp$.x_lab
  pp$.box      <- interaction(pp$.x_idx, pp$.s_idx)
  pp$.line     <- interaction(pp$.id, pp$.s_idx)
  
  summ <- pp %>%
    group_by(.x_lab, .s_lab, .pos, .col) %>%
    summarise(n = n(), M = mean(y), SD = sd(y), Mdn = median(y), .groups = "drop")
  
  cat("\n--- Participant-level summary (one value per participant per cell) ---\n")
  print_summ <- summ %>% ungroup() %>% select(.x_lab, .s_lab, n, M, SD, Mdn) %>% mutate(across(c(M, SD, Mdn), ~ round(.x, 3)))
  names(print_summ)[1:2] <- c(x_var, if (has_split) split_var else "split")
  if (!has_split) print_summ <- print_summ[, -2]
  print(as.data.frame(print_summ), row.names = FALSE)
  
  cols <- .fig_pick_colours(colours, if (dodge) n_s else n_x)
  bw   <- if (dodge) box_width / n_s else box_width
  
  p <- ggplot(pp, aes(colour = .col, fill = .col))
  if (connect_lines) {
    p <- p + geom_line(aes(x = .pos_j, y = y, group = .line), inherit.aes = FALSE,
                       colour = "grey50", alpha = line_alpha, linewidth = 0.4)
  }
  p <- p +
    geom_boxplot(aes(x = .pos, y = y, group = .box), width = bw, alpha = box_alpha,
                 outlier.shape = NA, linewidth = 0.6) +
    geom_point(aes(x = .pos_j, y = y), size = point_size, alpha = point_alpha, shape = 16)
  if (show_mean) {
    p <- p + geom_point(data = summ, aes(x = .pos, y = M), inherit.aes = FALSE,
                        shape = 23, size = 3, fill = "white", colour = "black")
  }
  if (has_split && !dodge) p <- p + facet_wrap(~ .s_lab, nrow = 1)
  
  p <- p +
    scale_colour_manual(values = cols, name = legend_title) +
    scale_fill_manual(values = cols,   name = legend_title) +
    scale_x_continuous(name = x_label, breaks = seq_len(n_x), labels = x_labels) +
    scale_y_continuous(name = y_label, breaks = .fig_breaks(y_limits, y_by)) +
    coord_cartesian(xlim = c(0.5, n_x + 0.5), ylim = y_limits) +
    labs(title = title) +
    .fig_theme(base_size, legend_position, legend_inside, legend_box,
               title_size, subtitle_size, axis_title_size, axis_text_size,
               legend_title_size, legend_text_size, panel_title_size)
  
  if (!dodge) p <- p + guides(colour = "none", fill = "none")
  p
}


## --- 5.5 panel grid: effect of the IV at each level of a moderator ----------
plot_panels_by_level <- function(model, data, focal, moderator, raw_mod_col,
                                 include       = list(),
                                 panel_by      = NULL,
                                 panel_values  = NULL, panel_labels = NULL,
                                 panel_prefix  = NULL, panel_digits = 2,
                                 ncol          = 3,
                                 x_limits      = c(-2, 2), x_by = 1,
                                 y_limits      = NULL,     y_by = NULL, free_y = FALSE,
                                 focal_values  = NULL,     focal_labels = NULL,
                                 x_label       = focal,    y_label = NULL,
                                 title         = NULL,
                                 colours       = "#2C3E6B",
                                 show_ci       = TRUE,     ci_alpha = 0.2, line_width = 1,
                                 show_data     = TRUE,     n_bins = 6, min_bin_n = 3,
                                 id_col        = "subject", data_colour = "grey35",
                                 hold_at       = "zero",   conf_level = 0.95,
                                 title_size      = NULL, subtitle_size  = NULL,
                                 axis_title_size = NULL, axis_text_size = NULL,
                                 panel_title_size = NULL,
                                 base_size     = 12) {
  data <- .fig_apply_include(as.data.frame(data), include)
  .fig_check_cols(data, c(focal, moderator, raw_mod_col, id_col, panel_by))
  dv       <- .fig_dv_name(model)
  is_glmer <- .fig_is_glmer(model)
  discrete <- !is.null(focal_values)
  holds    <- .fig_hold_from_include(data, model, exclude = c(focal, moderator))
  
  # panels are levels of the moderator itself, or of panel_by (e.g. stepIndex) if the moderator is messy
  level_col <- if (is.null(panel_by)) raw_mod_col else panel_by
  keep <- !is.na(data[[level_col]]) & !is.na(data[[dv]]) & !is.na(data[[raw_mod_col]])
  if (is.null(panel_values)) panel_values <- sort(unique(data[[level_col]][keep]))
  panel_values <- .fig_resolve_levels(data[[level_col]], panel_values, level_col)
  data$.p_idx  <- .fig_level_index(data[[level_col]], panel_values)
  
  if (length(panel_values) > 30) {
    stop(sprintf("'%s' has %d different values - too many for panels. Use panel_by = \"stepIndex\" (one panel per step), or panel_values = c(...) to pick a few.",
                 level_col, length(panel_values)))
  }
  if (length(panel_values) > 12) {
    cat(sprintf("\nNote: %d panels - that's a lot. Use panel_values = c(...) to pick a few, or panel_by = \"stepIndex\".\n",
                length(panel_values)))
  }
  mod_raw <- if (is.null(panel_by)) panel_values else
    vapply(seq_along(panel_values), function(k) mean(data[[raw_mod_col]][keep & data$.p_idx %in% k]), numeric(1))
  
  if (is.null(panel_prefix)) panel_prefix <- paste0(level_col, " = ")
  if (is.null(panel_labels)) {
    d_use <- panel_digits
    repeat {                                     # add decimal places if rounding makes two panel titles identical
      panel_labels <- paste0(panel_prefix, .fig_fmt_levels(panel_values, d_use))
      if (!any(duplicated(panel_labels)) || d_use >= 6) break
      d_use <- d_use + 1
    }
  }
  if (any(duplicated(panel_labels))) stop("Two or more panels have the same title - make panel_labels unique.")
  if (length(panel_labels) != length(panel_values)) stop("panel_labels needs one label per panel.")
  if (!is.null(panel_by)) {
    cat("\nPanels (with the average moderator value used for each):\n")
    print(data.frame(panel = panel_labels, moderator_value = round(mod_raw, 3)), row.names = FALSE)
  }
  if (is.null(y_label))  y_label  <- if (is_glmer) paste0("Predicted P(", dv, ")") else paste("Predicted", dv)
  if (is.null(y_limits) && is_glmer && !free_y) y_limits <- c(0, 1)
  if (is.null(x_limits) && !discrete) x_limits <- range(data[[focal]], na.rm = TRUE)
  if (discrete && is.null(focal_labels)) focal_labels <- .fig_fmt_levels(focal_values)
  
  z_vals <- .fig_raw_to_z(mod_raw, moderator, raw_mod_col, data)
  f_vals <- if (discrete) focal_values else seq(x_limits[1], x_limits[2], length.out = 150)
  
  grid <- expand.grid(.f = f_vals, .k = seq_along(panel_values))
  grid[[focal]]     <- grid$.f
  grid[[moderator]] <- z_vals[grid$.k]
  grid$.panel       <- factor(panel_labels[grid$.k], levels = panel_labels)
  pred <- .fig_predict(model, grid, hold_at = hold_at, hold_values = holds, conf_level = conf_level)
  if (discrete) pred$.f_lab <- factor(focal_labels[match(pred$.f, focal_values)], levels = focal_labels)
  
  if (!discrete) .fig_range_note(data[[focal]], x_limits, focal)
  
  # observed data: average within participant in each bin first, then across participants (+/- 1 SE)
  bd <- NULL
  if (show_data) {
    bins <- lapply(seq_along(panel_values), function(k) {
      rows <- data[data$.p_idx %in% k & !is.na(data[[dv]]) & !is.na(data[[focal]]), , drop = FALSE]
      if (discrete) {
        rows$.bin <- .fig_level_index(rows[[focal]], focal_values)
      } else {
        rows <- rows[rows[[focal]] >= x_limits[1] & rows[[focal]] <= x_limits[2], , drop = FALSE]
        rows$.bin <- cut(rows[[focal]], seq(x_limits[1], x_limits[2], length.out = n_bins + 1),
                         include.lowest = TRUE, labels = FALSE)
      }
      rows <- rows[!is.na(rows$.bin), , drop = FALSE]
      if (nrow(rows) == 0) return(NULL)
      rows %>%
        group_by(.id = .data[[id_col]], .bin) %>%
        summarise(m = mean(.data[[dv]]), fx = mean(.data[[focal]]), .groups = "drop") %>%
        group_by(.bin) %>%
        summarise(x = mean(fx), mean = mean(m), se = sd(m) / sqrt(n()), n = n(), .groups = "drop") %>%
        mutate(.panel = panel_labels[k])
    })
    bd <- bind_rows(bins)
    if (nrow(bd) > 0) {
      bd <- bd[bd$n >= min_bin_n, ]
      bd$.panel <- factor(bd$.panel, levels = panel_labels)
      if (discrete) bd$.f_lab <- factor(focal_labels[bd$.bin], levels = focal_labels)
    }
  }
  
  n_p  <- length(panel_values)
  cols <- if (length(colours) == 1) rep(colours, n_p) else .fig_pick_colours(colours, n_p)
  
  if (!discrete) {
    p <- ggplot(pred, aes(x = .f, y = fit))
    if (show_ci) p <- p + geom_ribbon(aes(ymin = lower, ymax = upper, fill = .panel), alpha = ci_alpha, colour = NA)
    if (!is.null(bd) && nrow(bd) > 0) {
      p <- p +
        geom_errorbar(data = bd, aes(x = x, ymin = mean - se, ymax = mean + se), inherit.aes = FALSE,
                      width = 0, colour = data_colour, alpha = 0.8) +
        geom_point(data = bd, aes(x = x, y = mean), inherit.aes = FALSE, colour = data_colour, size = 1.5)
    }
    p <- p + geom_line(aes(colour = .panel), linewidth = line_width) +
      scale_x_continuous(name = x_label, breaks = .fig_breaks(x_limits, x_by))
  } else {
    p <- ggplot(pred, aes(x = .f_lab, y = fit, colour = .panel, group = .panel))
    if (!is.null(bd) && nrow(bd) > 0) {
      p <- p + geom_point(data = bd, aes(x = .f_lab, y = mean), inherit.aes = FALSE,
                          colour = data_colour, shape = 1, size = 2,
                          position = position_nudge(x = 0.15))
    }
    p <- p + geom_line(linewidth = line_width * 0.7)
    if (show_ci) p <- p + geom_errorbar(aes(ymin = lower, ymax = upper), width = 0.1)
    p <- p + geom_point(size = 2.5) + labs(x = x_label)
  }
  
  p +
    facet_wrap(~ .panel, ncol = ncol, scales = if (free_y) "free_y" else "fixed") +
    scale_colour_manual(values = cols) +
    scale_fill_manual(values = cols) +
    guides(colour = "none", fill = "none") +
    scale_y_continuous(name = y_label, breaks = .fig_breaks(if (free_y) NULL else y_limits, y_by)) +
    coord_cartesian(xlim = if (discrete) NULL else x_limits, ylim = if (free_y) NULL else y_limits) +
    labs(title = title) +
    .fig_theme(base_size, "none", title_size = title_size, subtitle_size = subtitle_size,
               axis_title_size = axis_title_size, axis_text_size = axis_text_size,
               panel_title_size = panel_title_size)
}


## --- 5.6 metacognitive calibration panels (low / medium / high participant) -
plot_calibration_panels <- function(data, x_var, y_var,
                                    calib_var       = "meta_calibration_block",
                                    id_col          = "subject",
                                    include         = list(),
                                    subjects        = NULL,
                                    pick            = "min_median_max",
                                    probs           = c(0.10, 0.50, 0.90),
                                    n_sd            = 1,
                                    panel_labels    = c("Low calibration", "Medium calibration", "High calibration"),
                                    show_value      = TRUE, value_label = "r",
                                    show_id         = FALSE, min_rows = 20,
                                    x_label         = x_var, y_label = y_var, title = NULL,
                                    x_limits        = NULL, x_by = NULL,
                                    y_limits        = NULL, y_by = NULL,
                                    colours         = c("#C46B4E", "#D4A843", "#5B8C6A"),
                                    point_size      = 1.6, point_alpha = 0.4,
                                    jitter_width    = 0, jitter_height = 0,
                                    show_line       = TRUE, show_ci = TRUE, ci_alpha = 0.15,
                                    line_width      = 1, ncol = 3,
                                    title_size      = NULL, subtitle_size  = NULL,
                                    axis_title_size = NULL, axis_text_size = NULL,
                                    panel_title_size = NULL,
                                    base_size       = 13) {
  data <- .fig_apply_include(as.data.frame(data), include)
  .fig_check_cols(data, c(x_var, y_var, id_col, calib_var))
  data <- data[!is.na(data[[x_var]]) & !is.na(data[[y_var]]), , drop = FALSE]
  
  per <- data %>%
    group_by(.id = .data[[id_col]]) %>%
    summarise(n_rows = n(),
              r_plot = if (n() > 2) suppressWarnings(cor(.data[[x_var]], .data[[y_var]])) else NA_real_,
              .groups = "drop")
  
  # calibration score per participant (or the correlation in the plotted data if calib_var = NULL)
  if (is.null(calib_var)) {
    per$calib <- per$r_plot
  } else {
    cv <- data %>%
      group_by(.id = .data[[id_col]]) %>%
      summarise(calib  = mean(.data[[calib_var]], na.rm = TRUE),
                n_vals = n_distinct(.data[[calib_var]][!is.na(.data[[calib_var]])]), .groups = "drop")
    if (any(cv$n_vals > 1)) {
      cat(sprintf("\nWarning: '%s' has more than one value for %d participant(s) (e.g. more than one block) - these were averaged. Use include = list(task_name = ...) to keep one task.\n",
                  calib_var, sum(cv$n_vals > 1)))
    }
    per <- left_join(per, cv[, c(".id", "calib")], by = ".id")
    per$calib[is.nan(per$calib)] <- NA
  }
  
  eligible <- per[per$n_rows >= min_rows & !is.na(per$calib), ]
  cat(sprintf("\n%d of %d participants have a calibration score and at least %d rows to plot.\n",
              nrow(eligible), nrow(per), min_rows))
  if (nrow(eligible) == 0) stop("No eligible participants - check calib_var, include, or lower min_rows.")
  
  # choose the participants
  if (is.null(subjects)) {
    if (pick == "min_median_max") {
      chosen <- c(eligible$.id[which.min(eligible$calib)],
                  eligible$.id[which.min(abs(eligible$calib - median(eligible$calib)))],
                  eligible$.id[which.max(eligible$calib)])
    } else if (pick == "sd") {
      m <- mean(eligible$calib); s <- sd(eligible$calib)
      targets <- c(m - n_sd * s, m, m + n_sd * s)
      cat(sprintf("\nTargets (mean +/- %g SD of %s): %s\n", n_sd,
                  if (is.null(calib_var)) "the plotted correlation" else calib_var,
                  paste(round(targets, 3), collapse = ", ")))
      chosen <- vapply(targets, function(t) as.character(eligible$.id[which.min(abs(eligible$calib - t))]), character(1))
    } else if (pick == "quantiles") {
      qs     <- quantile(eligible$calib, probs = probs)
      chosen <- vapply(qs, function(q) as.character(eligible$.id[which.min(abs(eligible$calib - q))]), character(1))
    } else {
      stop("pick must be \"min_median_max\", \"sd\" or \"quantiles\" (or give subjects = c(...) yourself).")
    }
    chosen <- as.character(chosen)
    if (any(duplicated(chosen))) cat("\nNote: the same participant was picked for more than one panel - try another pick option or set subjects yourself.\n")
  } else {
    chosen <- as.character(subjects)
    not_found <- setdiff(chosen, as.character(per$.id))
    if (length(not_found) > 0) stop(sprintf("Participant(s) not found: %s", paste(not_found, collapse = ", ")))
  }
  
  n_p <- length(chosen)
  if (length(panel_labels) != n_p) {
    panel_labels <- paste("Participant", seq_len(n_p))
    cat("\nNote: panel_labels didn't match the number of participants, so generic labels were used.\n")
  }
  info <- per[match(chosen, as.character(per$.id)), ]
  full_labels <- panel_labels
  if (show_id)    full_labels <- paste0(full_labels, "\nID: ", info$.id)
  if (show_value) full_labels <- paste0(full_labels, "\n", value_label, " = ", .fig_apa_num(info$calib))
  
  cat("\n--- Participants plotted ---\n")
  print(data.frame(panel = panel_labels, id = info$.id, calibration = round(info$calib, 3),
                   r_in_plotted_rows = round(info$r_plot, 3), n_rows = info$n_rows), row.names = FALSE)
  
  pd <- data[as.character(data[[id_col]]) %in% chosen, , drop = FALSE]
  pd$.panel <- factor(full_labels[match(as.character(pd[[id_col]]), chosen)], levels = unique(full_labels))
  cols <- .fig_pick_colours(colours, n_p)
  
  p <- ggplot(pd, aes(x = .data[[x_var]], y = .data[[y_var]], colour = .panel, fill = .panel)) +
    geom_point(size = point_size, alpha = point_alpha,
               position = position_jitter(width = jitter_width, height = jitter_height, seed = 1))
  if (show_line) {
    p <- p + geom_smooth(method = "lm", formula = y ~ x, se = show_ci, alpha = ci_alpha, linewidth = line_width)
  }
  p +
    facet_wrap(~ .panel, ncol = ncol) +
    scale_colour_manual(values = cols) +
    scale_fill_manual(values = cols) +
    guides(colour = "none", fill = "none") +
    scale_x_continuous(name = x_label, breaks = .fig_breaks(x_limits, x_by)) +
    scale_y_continuous(name = y_label, breaks = .fig_breaks(y_limits, y_by)) +
    coord_cartesian(xlim = x_limits, ylim = y_limits) +
    labs(title = title) +
    .fig_theme(base_size, "none", title_size = title_size, subtitle_size = subtitle_size,
               axis_title_size = axis_title_size, axis_text_size = axis_text_size,
               panel_title_size = panel_title_size)
}


## --- 5.7 simple slopes for two (or more) models, with the data ------------

# simple slope of the focal predictor at each moderator value (same maths as get_simple_effects_flex)
.fig_simple_slopes <- function(model, data, focal, moderator, raw_mod_col, mod_values, conf_level = 0.95) {
  b <- lme4::fixef(model); V <- as.matrix(vcov(model))
  if (!focal %in% names(b)) stop(sprintf("'%s' isn't a predictor in one of the models.", focal))
  int <- intersect(c(paste0(focal, ":", moderator), paste0(moderator, ":", focal)), names(b))
  if (length(int) == 0) stop(sprintf("No %s x %s interaction in one of the models - 5.7 needs the interaction in every model.",
                                     focal, moderator))
  int <- int[1]
  z   <- .fig_raw_to_z(mod_values, moderator, raw_mod_col, data)
  est <- unname(b[focal] + b[int] * z)
  se  <- sqrt(V[focal, focal] + z^2 * V[int, int] + 2 * z * V[focal, int])
  crit <- qnorm(1 - (1 - conf_level) / 2)
  data.frame(raw_moderator = mod_values, z_moderator = z, b = est, se = se,
             lower = est - crit * se, upper = est + crit * se,
             p = 2 * pnorm(abs(est / se), lower.tail = FALSE))
}

# which moderator value each row belongs to: exact levels if every value is a real level, otherwise the nearest one
.fig_assign_levels <- function(x, mod_values) {
  exact <- all(vapply(mod_values, function(v) any(abs(x - v) < 1e-6, na.rm = TRUE), logical(1)))
  if (exact) {
    k <- .fig_level_index(x, mod_values)
  } else {
    o    <- order(mod_values)
    srt  <- mod_values[o]
    mids <- (srt[-1] + srt[-length(srt)]) / 2
    k    <- o[findInterval(x, mids) + 1]
  }
  list(k = k, exact = exact)
}

plot_model_slope_panels <- function(models, data, focal, moderator, raw_mod_col, mod_values,
                                    model_labels    = NULL, mod_labels = NULL,
                                    include         = list(),
                                    id_col          = "subject",
                                    show_data       = TRUE,
                                    data_points     = "auto",   # "participant", "binned", "raw" or "auto"
                                    x_bins          = 6,
                                    point_size      = 1.2,  point_alpha = 0.3, point_colour = NULL,
                                    show_ci         = TRUE, ci_alpha = 0.2, line_width = 1,
                                    show_values     = TRUE, value_digits = 2,
                                    free_y          = "auto",
                                    row_labels      = "right",  # "right" = beside each row; "left" = as each row's y-axis title
                                    row_label_angle = NULL,     # NULL = 90 on the left (reads upwards), 0 on the right (reads across)
                                    row_label_face  = NULL,     # NULL = "plain" on the left (like an axis title), "bold" on the right
                                    x_limits        = c(-2, 2), x_by = 1,
                                    y_limits        = NULL,     y_by = NULL,
                                    x_label         = NULL,     y_label = NULL,
                                    title           = NULL,     subtitle = NULL,
                                    colours         = NULL,
                                    hold_at         = "zero",   conf_level = 0.95, n_points = 150,
                                    legend_position = "none",   legend_inside = c(0.02, 0.98),
                                    legend_box      = TRUE,
                                    title_size      = NULL, subtitle_size    = NULL,
                                    axis_title_size = NULL, axis_text_size   = NULL,
                                    legend_title_size = NULL, legend_text_size = NULL,
                                    panel_title_size = NULL, value_text_size = 3,
                                    base_size       = 12) {
  if (inherits(models, "merMod")) models <- list(models)
  if (!is.list(models) || length(models) == 0) stop("models needs to be a list, e.g. models = list(model2, model3).")
  if (!data_points %in% c("auto", "participant", "binned", "raw")) {
    stop("data_points must be \"auto\", \"participant\", \"binned\" or \"raw\".")
  }
  if (!row_labels %in% c("right", "left")) stop("row_labels must be \"right\" or \"left\".")
  if (is.null(row_label_angle)) row_label_angle <- if (row_labels == "left") 90 else 0
  if (is.null(row_label_face))  row_label_face  <- if (row_labels == "left") "plain" else "bold"
  y_label_auto <- is.null(y_label)
  
  dats <- if (is.data.frame(data)) rep(list(data), length(models)) else data
  if (length(dats) != length(models)) stop("Give one data frame, or a list with one per model.")
  dats <- lapply(dats, function(dd) .fig_apply_include(as.data.frame(dd), include))
  
  dvs <- vapply(models, .fig_dv_name, character(1))
  if (is.null(model_labels)) model_labels <- paste0("Model ", seq_along(models), " (", dvs, ")")
  if (length(model_labels) != length(models)) stop("model_labels needs one label per model.")
  if (is.null(mod_labels))  mod_labels  <- .fig_mod_labels(mod_values, raw_mod_col, dats[[1]])
  if (length(mod_labels) != length(mod_values)) stop("mod_labels needs one label per value in mod_values.")
  if (identical(free_y, "auto")) free_y <- length(unique(dvs)) > 1
  if (is.null(x_label)) x_label <- focal
  if (is.null(y_label)) y_label <- if (row_labels == "left") NULL else          # left: the row labels ARE the axis titles
    if (length(unique(dvs)) == 1) dvs[1] else "Outcome"
  if (is.null(x_limits)) x_limits <- range(dats[[1]][[focal]], na.rm = TRUE)
  
  # ---- the simple slopes (numbers for every panel) ----
  slopes <- bind_rows(lapply(seq_along(models), function(i) {
    out <- .fig_simple_slopes(models[[i]], dats[[i]], focal, moderator, raw_mod_col, mod_values, conf_level)
    out$.model <- model_labels[i]; out$.level <- mod_labels
    out
  }))
  slopes$.model <- factor(slopes$.model, levels = model_labels)
  slopes$.level <- factor(slopes$.level, levels = mod_labels)
  
  cat("\n--- Simple effects of ", focal, " at each level of ", raw_mod_col, " ---\n", sep = "")
  print(data.frame(model = slopes$.model, level = slopes$.level,
                   b = round(slopes$b, 3), SE = round(slopes$se, 3),
                   CI_lower = round(slopes$lower, 3), CI_upper = round(slopes$upper, 3),
                   p = ifelse(slopes$p < .001, "< .001", .fig_apa_num(slopes$p, 3)),
                   significant = slopes$p < .05), row.names = FALSE)
  if (any(vapply(models, .fig_is_glmer, logical(1)))) {
    cat("\nNote: for glmer models b is in log-odds (the curves show probabilities).\n")
  }
  if (length(unique(dvs)) > 1) {
    cat("\nNote: the models have different outcomes (", paste(unique(dvs), collapse = ", "),
        "), so each row gets its own y-axis.\n", sep = "")
  }
  
  # ---- the predicted line at each level, for each model ----
  pred <- bind_rows(lapply(seq_along(models), function(i) {
    z_mod <- .fig_raw_to_z(mod_values, moderator, raw_mod_col, dats[[i]])
    grid  <- expand.grid(.f = seq(x_limits[1], x_limits[2], length.out = n_points), .k = seq_along(mod_values))
    grid[[focal]]     <- grid$.f
    grid[[moderator]] <- z_mod[grid$.k]
    out <- .fig_predict(models[[i]], grid, hold_at = hold_at,
                        hold_values = .fig_hold_from_include(dats[[i]], models[[i]], c(focal, moderator)),
                        conf_level = conf_level)
    out$.model <- model_labels[i]; out$.level <- mod_labels[out$.k]
    out
  }))
  pred$.model <- factor(pred$.model, levels = model_labels)
  pred$.level <- factor(pred$.level, levels = mod_labels)
  
  # ---- the observed data at each level (unadjusted) ----
  pts <- NULL
  if (show_data) {
    pts <- bind_rows(lapply(seq_along(models), function(i) {
      dd <- dats[[i]]; dv <- dvs[i]
      .fig_check_cols(dd, c(dv, focal, raw_mod_col, id_col))
      dd <- dd[!is.na(dd[[dv]]) & !is.na(dd[[focal]]) & !is.na(dd[[raw_mod_col]]), , drop = FALSE]
      asg <- .fig_assign_levels(dd[[raw_mod_col]], mod_values)
      dd$.k <- asg$k
      dd <- dd[!is.na(dd$.k), , drop = FALSE]
      if (i == 1) {
        cat(if (asg$exact) "\nData in each column: rows at exactly that moderator level.\n" else
          "\nData in each column: rows whose moderator value is closest to that column's value (the moderator is split into bands).\n")
      }
      mode <- data_points
      if (mode == "auto") {
        within <- dd %>% group_by(.data[[id_col]]) %>% summarise(v = n_distinct(.data[[focal]]), .groups = "drop")
        mode <- if (mean(within$v > 1) > 0.5) "binned" else "participant"
      }
      if (mode == "participant") {
        out <- dd %>% group_by(.k, .id = .data[[id_col]]) %>%
          summarise(x = mean(.data[[focal]]), y = mean(.data[[dv]]), .groups = "drop")
      } else if (mode == "binned") {
        dd <- dd[dd[[focal]] >= x_limits[1] & dd[[focal]] <= x_limits[2], , drop = FALSE]
        dd$.bin <- cut(dd[[focal]], seq(x_limits[1], x_limits[2], length.out = x_bins + 1),
                       include.lowest = TRUE, labels = FALSE)
        out <- dd %>% group_by(.k, .id = .data[[id_col]], .bin) %>%
          summarise(x = mean(.data[[focal]]), y = mean(.data[[dv]]), .groups = "drop")
      } else {
        out <- data.frame(.k = dd$.k, .id = dd[[id_col]], x = dd[[focal]], y = dd[[dv]])
      }
      if (i == 1) {
        cat(sprintf("Each dot: %s.\n", switch(mode,
                                              participant = "one participant (their average at that level)",
                                              binned      = sprintf("one participant within one of %d x bins", x_bins),
                                              raw         = "one row of the data")))
      }
      out$.model <- model_labels[i]; out$.level <- mod_labels[out$.k]
      out
    }))
    pts$.model <- factor(pts$.model, levels = model_labels)
    pts$.level <- factor(pts$.level, levels = mod_labels)
  }
  
  cols <- .fig_pick_colours(colours, length(models))
  names(cols) <- model_labels
  
  p <- ggplot(pred, aes(x = .f, y = fit, colour = .model, fill = .model))
  if (!is.null(pts) && nrow(pts) > 0) {
    if (is.null(point_colour)) {
      p <- p + geom_point(data = pts, aes(x = x, y = y, colour = .model), inherit.aes = FALSE,
                          size = point_size, alpha = point_alpha, shape = 16)
    } else {
      p <- p + geom_point(data = pts, aes(x = x, y = y), inherit.aes = FALSE,
                          size = point_size, alpha = point_alpha, shape = 16, colour = point_colour)
    }
  }
  if (show_ci) p <- p + geom_ribbon(aes(ymin = lower, ymax = upper), alpha = ci_alpha, colour = NA)
  p <- p + geom_line(linewidth = line_width)
  if (show_values) {
    slopes$.lab <- paste0("b = ", formatC(slopes$b, format = "f", digits = value_digits), ", ",
                          ifelse(slopes$p < .001, "p < .001", paste("p =", .fig_apa_num(slopes$p, 3))))
    p <- p + geom_text(data = slopes, aes(x = -Inf, y = Inf, label = .lab), inherit.aes = FALSE,
                       hjust = -0.06, vjust = 1.4, size = value_text_size, colour = "grey25")
  }
  
  p <- p +
    facet_grid(.model ~ .level, scales = if (free_y) "free_y" else "fixed",
               switch = if (row_labels == "left") "y" else NULL) +
    scale_colour_manual(values = cols, name = NULL) +
    scale_fill_manual(values = cols, name = NULL) +
    scale_x_continuous(name = x_label, breaks = .fig_breaks(x_limits, x_by)) +
    scale_y_continuous(name = y_label, breaks = .fig_breaks(if (free_y) NULL else y_limits, y_by),
                       expand = if (show_values) expansion(mult = c(0.05, 0.18)) else waiver()) +
    coord_cartesian(xlim = x_limits, ylim = if (free_y) NULL else y_limits) +
    labs(title = title, subtitle = subtitle) +
    .fig_theme(base_size, legend_position, legend_inside, legend_box,
               title_size, subtitle_size, axis_title_size, axis_text_size,
               legend_title_size, legend_text_size, panel_title_size)
  if (row_labels == "left") {
    p <- p + theme(strip.placement   = "outside",      # outside the axis numbers, where a y-axis title would sit
                   strip.text.y.left = element_text(angle = row_label_angle, face = row_label_face,
                                                    size = if (is.null(axis_title_size)) base_size else axis_title_size))
    if (y_label_auto) p <- p + labs(y = NULL)
  } else {
    p <- p + theme(strip.text.y = element_text(angle = row_label_angle, face = row_label_face))
  }
  p
}

#--------#


## --- 5.8 descriptive panel grid (no model) ----------------------------------
plot_descriptive_panels <- function(data, x_var, y_var, panel_by,
                                    id_col          = "subject",
                                    include         = list(),
                                    panel_values    = NULL, panel_labels = NULL,
                                    panel_prefix    = NULL, panel_digits = 2,
                                    ncol            = 3,
                                    average_within  = TRUE,   # TRUE = one dot per participant per panel
                                    x_bins          = NULL,   # bin x first (e.g. 6) when x varies within participants
                                    x_limits        = NULL, x_by = NULL,
                                    y_limits        = NULL, y_by = NULL, free_y = FALSE,
                                    x_label         = x_var, y_label = NULL,
                                    title           = NULL, subtitle = NULL,
                                    colours         = "#2C3E6B",
                                    point_size      = 1.4, point_alpha = 0.35,
                                    show_line       = TRUE, line_method = "lm",
                                    show_ci         = TRUE, ci_alpha = 0.15, line_width = 0.9,
                                    show_r          = FALSE, r_text_size = 3.2,
                                    title_size      = NULL, subtitle_size  = NULL,
                                    axis_title_size = NULL, axis_text_size = NULL,
                                    panel_title_size = NULL,
                                    base_size       = 12) {
  data <- .fig_apply_include(as.data.frame(data), include)
  .fig_check_cols(data, c(x_var, y_var, panel_by, id_col))
  data <- data[!is.na(data[[x_var]]) & !is.na(data[[y_var]]) & !is.na(data[[panel_by]]), , drop = FALSE]
  if (nrow(data) == 0) stop("No rows left to plot - check the variable names and include.")
  
  if (is.null(panel_values)) panel_values <- sort(unique(data[[panel_by]]))
  panel_values <- .fig_resolve_levels(data[[panel_by]], panel_values, panel_by)
  if (length(panel_values) > 30) {
    stop(sprintf("'%s' has %d different values - too many for panels. Use panel_values = c(...) to pick a few, or a variable with fewer levels (e.g. stepIndex).",
                 panel_by, length(panel_values)))
  }
  data$.p_idx <- .fig_level_index(data[[panel_by]], panel_values)
  data <- data[!is.na(data$.p_idx), , drop = FALSE]
  
  if (is.null(panel_prefix)) panel_prefix <- paste0(panel_by, " = ")
  if (is.null(panel_labels)) {
    d_use <- panel_digits
    repeat {
      panel_labels <- paste0(panel_prefix, .fig_fmt_levels(panel_values, d_use))
      if (!any(duplicated(panel_labels)) || d_use >= 6) break
      d_use <- d_use + 1
    }
  }
  if (length(panel_labels) != length(panel_values)) stop("panel_labels needs one label per panel.")
  if (any(duplicated(panel_labels))) stop("Two or more panels have the same title - make panel_labels unique.")
  
  # what each dot is: a participant (optionally within an x bin), or a raw row
  if (!is.null(x_bins)) {
    rng <- if (is.null(x_limits)) range(data[[x_var]], na.rm = TRUE) else x_limits
    data <- data[data[[x_var]] >= rng[1] & data[[x_var]] <= rng[2], , drop = FALSE]
    data$.bin <- cut(data[[x_var]], seq(rng[1], rng[2], length.out = x_bins + 1),
                     include.lowest = TRUE, labels = FALSE)
    pp <- data %>%
      group_by(.p_idx, .id = .data[[id_col]], .bin) %>%
      summarise(x = mean(.data[[x_var]]), y = mean(.data[[y_var]]), .groups = "drop")
    dot_is <- sprintf("one dot per participant per x bin (%d bins)", x_bins)
  } else if (average_within) {
    pp <- data %>%
      group_by(.p_idx, .id = .data[[id_col]]) %>%
      summarise(x = mean(.data[[x_var]]), y = mean(.data[[y_var]]), .groups = "drop")
    dot_is <- "one dot per participant"
  } else {
    pp <- data.frame(.p_idx = data$.p_idx, .id = data[[id_col]], x = data[[x_var]], y = data[[y_var]])
    dot_is <- "one dot per row of the data"
  }
  pp$.panel <- factor(panel_labels[pp$.p_idx], levels = panel_labels)
  if (is.null(y_label)) y_label <- if (average_within || !is.null(x_bins)) paste("Mean", y_var) else y_var
  
  # what's actually being plotted, for checking and reporting
  summ <- pp %>%
    group_by(.panel) %>%
    summarise(n_dots = n(), n_participants = n_distinct(.id),
              M_y = mean(y), SD_y = sd(y),
              r = if (n() >= 4) suppressWarnings(cor(x, y)) else NA_real_, .groups = "drop")
  cat(sprintf("\n--- Descriptive panels: %s ---\n", dot_is))
  print(as.data.frame(summ %>% mutate(across(c(M_y, SD_y, r), ~ round(.x, 3)))), row.names = FALSE)
  
  cols <- if (length(colours) == 1) rep(colours, length(panel_values)) else
    .fig_pick_colours(colours, length(panel_values))
  
  p <- ggplot(pp, aes(x = x, y = y, colour = .panel, fill = .panel)) +
    geom_point(size = point_size, alpha = point_alpha)
  if (show_line) {
    p <- p + geom_smooth(method = line_method, formula = y ~ x, se = show_ci,
                         alpha = ci_alpha, linewidth = line_width)
  }
  if (show_r) {
    lab <- summ %>% mutate(lab = ifelse(is.na(r), "", paste0("r = ", .fig_apa_num(r))))
    p <- p + geom_text(data = lab, aes(x = -Inf, y = Inf, label = lab), inherit.aes = FALSE,
                       hjust = -0.15, vjust = 1.4, size = r_text_size, colour = "grey25")
  }
  
  p +
    facet_wrap(~ .panel, ncol = ncol, scales = if (free_y) "free_y" else "fixed") +
    scale_colour_manual(values = cols) +
    scale_fill_manual(values = cols) +
    guides(colour = "none", fill = "none") +
    scale_x_continuous(name = x_label, breaks = .fig_breaks(x_limits, x_by)) +
    scale_y_continuous(name = y_label, breaks = .fig_breaks(if (free_y) NULL else y_limits, y_by)) +
    coord_cartesian(xlim = x_limits, ylim = if (free_y) NULL else y_limits) +
    labs(title = title, subtitle = subtitle) +
    .fig_theme(base_size, "none", title_size = title_size, subtitle_size = subtitle_size,
               axis_title_size = axis_title_size, axis_text_size = axis_text_size,
               panel_title_size = panel_title_size)
}


## --- 5.9 frequency bars with participant dots -------------------------------
plot_frequency_bars <- function(data, x_var, id_col = "subject",
                                one_row_per     = NULL,      # e.g. c("subject", "trialIndex") to count TRIALS, not rows
                                include         = list(),
                                x_levels        = NULL, x_labels = NULL,
                                y_unit          = "percent", # "percent" or "count"
                                bar_stat        = "pooled",  # "pooled" = % of all trials; "participants" = mean of each participant's %
                                show_labels     = TRUE, label_digits = 1, label_size = 3.2,
                                show_points     = TRUE, point_size = 1.3, point_alpha = 0.45,
                                jitter_width    = 0.12, point_colour = "grey25",
                                show_error      = FALSE, error_type = "se",
                                bar_fill        = "grey65", bar_colour = "grey20",
                                bar_width       = 0.75, bar_alpha = 1, colours = NULL,
                                x_label         = x_var, y_label = NULL,
                                title           = NULL, subtitle = NULL,
                                y_limits        = NULL, y_by = NULL,
                                title_size      = NULL, subtitle_size  = NULL,
                                axis_title_size = NULL, axis_text_size = NULL,
                                base_size       = 13, seed = 1) {
  data <- .fig_apply_include(as.data.frame(data), include)
  .fig_check_cols(data, c(x_var, id_col, one_row_per))
  if (!y_unit %in% c("percent", "count")) stop("y_unit must be \"percent\" or \"count\".")
  if (!bar_stat %in% c("pooled", "participants")) stop("bar_stat must be \"pooled\" or \"participants\".")
  
  # one row per trial (or whatever you name), so repeated step rows aren't counted many times
  if (!is.null(one_row_per)) {
    keys <- one_row_per
    vars <- setdiff(c(x_var, id_col), keys)
    n_before <- nrow(data)
    data <- data %>%
      group_by(across(all_of(keys))) %>%
      summarise(across(all_of(vars), ~ { v <- .x[!is.na(.x)]; if (length(v) == 0) .x[NA_integer_] else v[1] }),
                .groups = "drop") %>%
      as.data.frame()
    cat(sprintf("\nOne row per %s: %d rows kept from %d.\n",
                paste(keys, collapse = " x "), nrow(data), n_before))
  }
  data <- data[!is.na(data[[x_var]]) & !is.na(data[[id_col]]), , drop = FALSE]
  if (nrow(data) == 0) stop("No rows left to count - check the variable names and include.")
  
  if (is.null(x_levels)) x_levels <- sort(unique(data[[x_var]]))
  x_levels <- .fig_resolve_levels(data[[x_var]], x_levels, x_var)
  if (is.null(x_labels)) x_labels <- .fig_fmt_levels(x_levels)
  if (length(x_labels) != length(x_levels)) stop("x_labels needs one label per level in x_levels.")
  data$.x_idx <- .fig_level_index(data[[x_var]], x_levels)
  dropped <- sum(is.na(data$.x_idx))
  if (dropped > 0) cat(sprintf("\nNote: %d row(s) are at levels you didn't include and were left out of the percentages.\n", dropped))
  data <- data[!is.na(data$.x_idx), , drop = FALSE]
  
  # overall counts, and each participant's own counts (participants with none of a level count as 0)
  overall <- data %>%
    group_by(.x_idx) %>% summarise(n = n(), .groups = "drop") %>%
    right_join(data.frame(.x_idx = seq_along(x_levels)), by = ".x_idx") %>%
    mutate(n = ifelse(is.na(n), 0L, n), pct = 100 * n / sum(n))
  
  per_id <- data %>%
    group_by(.id = .data[[id_col]], .x_idx) %>% summarise(n = n(), .groups = "drop") %>%
    tidyr::complete(.id, .x_idx = seq_along(x_levels), fill = list(n = 0L)) %>%
    group_by(.id) %>% mutate(pct = 100 * n / sum(n)) %>% ungroup()
  
  per_id$value  <- if (y_unit == "percent") per_id$pct else per_id$n
  overall$value <- if (y_unit == "percent") overall$pct else overall$n
  
  summ <- per_id %>% group_by(.x_idx) %>%
    summarise(mean_value = mean(value), sd = sd(value), n_id = n(), .groups = "drop") %>%
    mutate(se = sd / sqrt(n_id),
           crit = qt(0.975, pmax(n_id - 1, 1)),
           lower = mean_value - if (error_type == "ci") crit * se else se,
           upper = mean_value + if (error_type == "ci") crit * se else se)
  bars <- overall %>% left_join(summ, by = ".x_idx")
  bars$height <- if (bar_stat == "pooled") bars$value else bars$mean_value
  
  if (show_error && bar_stat == "pooled") {
    cat("\nNote: error bars describe variation between participants, so they only fit bar_stat = \"participants\" - not drawn here.\n")
  }
  
  bars$.x_lab   <- factor(x_labels[bars$.x_idx],   levels = x_labels)
  per_id$.x_lab <- factor(x_labels[per_id$.x_idx], levels = x_labels)
  
  # the label goes above whatever is tallest in that column: the bar, the error bar, or the highest dot
  top_dot <- per_id %>% group_by(.x_idx) %>% summarise(top = max(value), .groups = "drop")
  bars <- bars %>% left_join(top_dot, by = ".x_idx")
  bars$.label_y <- bars$height
  if (show_error && bar_stat == "participants") bars$.label_y <- pmax(bars$.label_y, bars$upper, na.rm = TRUE)
  if (show_points) bars$.label_y <- pmax(bars$.label_y, bars$top, na.rm = TRUE)
  if (!is.null(y_limits)) {                          # keep labels inside the panel when you've set the y range
    bars$.label_y <- pmin(bars$.label_y, y_limits[2] - 0.05 * diff(y_limits))
  }
  if (is.null(y_label)) y_label <- if (y_unit == "percent") "Percentage" else "Count"
  
  cat(sprintf("\n--- %s of %s (%d rows, %d participants) ---\n",
              if (y_unit == "percent") "Percentages" else "Counts", x_var, nrow(data), n_distinct(data[[id_col]])))
  print(data.frame(level = bars$.x_lab, n = bars$n, percent = round(bars$pct, 2),
                   participant_M = round(bars$mean_value, 2), participant_SD = round(bars$sd, 2)),
        row.names = FALSE)
  
  fills <- if (is.null(colours)) rep(bar_fill, length(x_levels)) else .fig_pick_colours(colours, length(x_levels))
  set.seed(seed)
  
  p <- ggplot(bars, aes(x = .x_lab, y = height)) +
    geom_col(aes(fill = .x_lab), colour = bar_colour, width = bar_width, alpha = bar_alpha)
  if (show_error && bar_stat == "participants") {
    p <- p + geom_errorbar(aes(ymin = lower, ymax = upper), width = 0.15, colour = bar_colour)
  }
  if (show_points) {
    p <- p + geom_point(data = per_id, aes(x = .x_lab, y = value), inherit.aes = FALSE,
                        position = position_jitter(width = jitter_width, height = 0, seed = seed),
                        size = point_size, alpha = point_alpha, colour = point_colour, shape = 16)
  }
  if (show_labels) {
    lab <- if (y_unit == "percent") paste0(formatC(bars$height, format = "f", digits = label_digits), "%") else
      .fig_fmt_levels(bars$height, label_digits)
    p <- p + geom_text(aes(y = .label_y, label = lab), vjust = -0.6, size = label_size)
  }
  
  p +
    scale_fill_manual(values = fills) +
    guides(fill = "none") +
    scale_y_continuous(name = y_label, breaks = .fig_breaks(y_limits, y_by),
                       expand = expansion(mult = c(0, 0.10))) +
    labs(x = x_label, title = title, subtitle = subtitle) +
    coord_cartesian(ylim = y_limits) +
    .fig_theme(base_size, "none", title_size = title_size, subtitle_size = subtitle_size,
               axis_title_size = axis_title_size, axis_text_size = axis_text_size)
}

#--------#


## variable dictionary
# expand with the arrow on the left to see definitions of all of the variables
# coding and units are indicated in brackets qhere appropriate --------#


## setup and diagnostics
# subject                       --  unique participant ID
# key_mapping                   --  side of response buttons (1 = red/blue, 2 = blue/red on left/right, respectively)
# mouse_hand                    --  hand selected for mouse use (right, left)
# mouse_or_trackpad             --  mouse or trackpad selected (mouse, trackpad)
# browser_user_agent            --  browser’s identification string (shows browser, version and operating system)
# screen_width                  --  (pixels)
# screen_height                 --  (pixels)
# study                         --  which study they were part of (feedback or termination)


## blocks and timing
# task_name                     --  name of task in block (maintask, feedback, searchtermination)
# total_time                    --  total time taken, per block (ms)
# instruction_time              --  time taken on pre-task instructions, per block (ms) 
# task_time                     --  time taken on all trials, per block (ms)
# total_fullscreen_prompts      --  number of times participants saw prompt to return to fullscreen (numeric, 0 if the participant never left full screen)


## manipulation checks
# manip_check_attempts          --  number of attempts for pre-task goal check, per block (numeric, 1 if the participant was correct first-try)
# manip_check_post_attempts     --  number of attempts for "which guesses count" check, per block (numeric, 1 if the participant was correct first-try; presented main task only)
# manip_check_post_passed       --  whether the post-task check ended on a correct answer, per block (1 = Yes, 0 = No).
# score_check_attempts          --  number of attempts for "which guesses count" check, per block (numeric, 1 if the participant was correct first-try)
# scale_check_unsure_attempts   --  number of attempts for "show how you would answer if very unsure" (numeric, 1 if the participant was correct first-try; presented main task only)
# scale_check_sure_attempts     --  number of attempts for "show how you would answer if very sure" (numeric, 1 if the participant was correct first-try; presented main task only)


## demographics
# vision_prolific	              --  response to "Do you have normal or corrected-to-normal vision?" (Yes, No, Rather not say)
# colourblindness_prolific	    --	response to "Do you experience colourblindness?" (Yes, I'm colourblind; No, I have no issues seeing colours; Rather not say)
# age_prolific		              --  age in years
# sex_prolific		              --  response to "What is your sex, as recorded on legal/official documents?" (Male, Female)
# gender_prolific	              --	response to "What gender are you currently? We will ask about your sex later." (Man (including Trans Male/Trans Man); Woman (including Trans Female/Trans Woman); 
#  Non-binary (would like to give more detail); Rather not say))
# postcode_prolific		          --  response to "In which postcode area do you live?" (121 options, two letter code)
# ethnicity_prolific		        --  response to "What ethnic group do you belong to?" (White, Black, Asian, Mixed, Other, Prefer not to say)
# country_birth_prolific        --	response to "What is your country of birth?" (248 options)
# country_residence_prolific	  --  response to "In what country do you currently reside?" (246 options)
# nationality_prolific	        --  response to "What is your nationality?" (246 options)
# language_prolific	            --  response to "What is your first language?" (90 options)
# student_prolific	            --  response to "Are you a student?" (Yes, No)
# employment_prolific           --  response to "Employment Status" (Full-Time; Part-Time; Due to start a new job within the next month; Unemployed (and job seeking); 
#  Not in paid work (e.g. homemaker', 'retired or disabled); Other)


## trial parameters 
# trialIndex                    --  trial order (1-32, or 1-64 in termination; feedback practice grid shows as 0)
# stepIndex                     --  step number in each trial (1-9)
# runID                         --  which of the grid were presented, per trial (1-32, 1-16 are base, 17-32 are colour-swapped)
# runID_type                    --  grid types from above collapsed into the 16 unique types (2 per runID_type for main task and feedback, 4 for termination)
# swapped                       --  whether the grid was a base or colour-swapped (0 and 1, respectively)
# crossings                     --  number of times the visible majority switches, per trial
# random_selected               --  the colour randomly selected by computer (red, blue)
# trial_time                    --  time taken, per trial (ms)
# too_slow_screen               --  whether response was made after deadline (1 = Yes, 0 = No)
# final_majority_color          --  the colour with more balls in the complete grid (red, blue; termination only)
# finalTotalBlue                --  number of blue balls in full grid
# finalTotalRed                 --  number of red balls in full grid


## step parameters 
# countClosed                   --  number of boxes closed, per step (0-256)
# countOpen                     --  number of visible balls at current step (0-256)
# countBlue                     --  number of visible blue balls, per step (cumulative)
# countRed                      --  number of visible red balls, per step (cumulative)
# prevBlue                      --  number of blue balls visible at previous step (n-1)
# prevRed                       --  number of red balls visible at previous step (n-1)
# newBlue                       --  number of blue balls revealed at current step
# newRed                        --  number of red balls revealed at current step
## normalised step parameters (based on chosen)
## NOTE: prop_old_chosen + prop_old_nonchosen + prop_new_chosen + prop_new_nonchosen = 1
# prop_old_chosen               --  proportion of previously visible balls matching guessed colour (revealed n-1)
# prop_old_nonchosen            --  proportion of previously visible balls opposite to guessed colour (revealed n-1)
# prop_new_chosen               --  proportion of newly revealed balls matching guessed colour (revealed n)
# prop_new_nonchosen            --  proportion of newly revealed balls opposite to guessed colour (revealed n)
##
# propKnownEvidence             --  proportion of the grid visible at current step (0-1)
##
# NOTE: prop_chosen + prop_nonchosen = 1
# prop_chosen                   --  proportion of visible balls matching guessed colour
# prop_nonchosen                --  proportion of visible balls opposite to guessed colour
# NOTE: prop_old_notlastchosen + prop_new_notlastchosen = 1
# prop_old_notlastchosen        --  proportion of previously visible balls for the colour not guessed last time
# prop_new_notlastchosen        --  proportion of newly visible balls for the colour not guessed last time
# crossing_moment               --  whether the majority colour flipped on current step


## primary task responses
# choice                        --  colour selected, per step (red, blue)
# choiceRT                      --  response time for colour guess (ms, measured from onset of new information fade in)
# early_choice                  --  whether a response was made before allowed (i.e., before new information onset; 1 = Yes, 0 = No)
# confidence                    --  scale rating (0-256)
# confRT                        --  time taken to give confidence rating (ms)
# prevConfidence                --  confidence rating for prior guess (n-1, blank in first row)
# prevChoiceRT                  --  choice reaction time for prior guess (n-1, blank in first row)


## computed variables
# change_of_mind                --  whether guess differs from previous prior guess (1 = Yes, 0 = No; blank on step 1 of each trial)
# should_change                 --  whether previous guess differs from current correct (1 = Yes, 0 = No; blank on step 1 of each trial) 
# rational_decision             --  whether guess matched the current visible majority (1 = Yes, 0 = No)
# rational_change_of_mind       --  whether a change of mind matched the current visible majority (change of mind trials only; 1 = toward majority, 0 = against majority) 
# choice_matches_final_majority --  whether guess matched the final majority (1 = Yes, 0 = No; termination only) 
# choice_probability_correct    --  probability choice is correct based on final grid 
# choice_matches_selected       --  whether guess matched the randomly selected box (1 = Yes, 0 = No; main task and feedback only) 
# cumulative_step_changes       --  cumulative changes of mind at each step, per trial (start at 0 each trial and adds on each step if a change of mind occurs)
# total_trial_changes           --  total changes of mind, per trial (final value of )
# meta_calibration_block        --  confidence to evidence correlation computed, per block (Pearson correlation pooled across all rated guesses on steps 2–9 of every trial in a block; 
#  practice excluded and only commit choice in termination





## termination only variables
# commit_margin                 --  strength of visible evidence in favour of chosen option at commit (positive is majority selected; termination only) 
# commit                        --  whether participant chose to commit, per step (1 = Yes, 0 = No, NA on step 1 of each trial)
# commit_correct_final_majority --  whether the guess at commit was correct (1 = Yes, 0 = No; termination only)
# points                        --  points won or lost, per trial (+/- 10 to 80; termination only)
# whichever row has confidence - get the step 

## feedback only variables
# prev_feedback_label           --  label of performance on previous trial (always_right, mostly_right, mostly_wrong, always_wrong)  
# prev_feedback_valence         --  whether feedback on the previous trial was positive (majority right = 1) or negative (majority wrong = 0)
# recent_feedback               --  proportion of correct guesses on previous trial (0-1, blank on practice trial/trialIndex = 0)
# cumulative_feedback           --  cumulative mean of proportion correct on all previous trials (0-1, blank on practice trial/trialIndex = 0)
# feedback_screen_time          --  time viewing feedback screen on current trial (n; ms)
# prev_feedback_time            --  time viewing feedback on previous trial (n-1; ms)



## rational termination - most points and divergence 
## ratinonal change of mind - signal detection theory - misses more - should_change - is your answer on prev difference from correct current - and change the other one to did you change yes or no - NA on step 1
## metacog in feedback - meta-d' only 

## survey variables - see "survey items dictionary" section below for scales and scoring
# big5_duration_ms              --  time spent on big5 survey (page load to click to proceed; ms)	
# big5_skipped_ahead	          --  whether participant proceeded with unanswered questions (1 = Yes; 0 = No)
# ih_duration_ms	              --  time spent on ih survey (page load to click to proceed; ms)	
# ih_skipped_ahead	            --  whether participant proceeded with unanswered questions (1 = Yes; 0 = No)
# lo_duration_ms	              --  time spent on lo survey (page load to click to proceed; ms)	
# lo_skipped_ahead	            --  whether participant proceeded with unanswered questions (1 = Yes; 0 = No)
# bis_duration_ms	              --  time spent on bias survey (page load to click to proceed; ms)	
# bis_skipped_ahead	            --  whether participant proceeded with unanswered questions (1 = Yes; 0 = No)
# i8_duration_ms	              --  time spent on i8 survey (page load to click to proceed; ms)	
# i8_skipped_ahead	            --  whether participant proceeded with unanswered questions (1 = Yes; 0 = No)
# bscs_duration_ms	            --  time spent on bscs survey (page load to click to proceed; ms)	
# bscs_skipped_ahead	          --  whether participant proceeded with unanswered questions (1 = Yes; 0 = No)
# grips_duration_ms	            --  time spent on grips survey (page load to click to proceed; ms)	
# grips_skipped_ahead           --  whether participant proceeded with unanswered questions (1 = Yes; 0 = No)

#--------#

## survey items dictionary
# expand with the arrow on the left to see the items and coding in each survey 
# NOTE: when you use these variables, only copy the item name (e.g., big5_01) --------#


## BIG 5 - mini-IPIP (20 items, score 1-5)
# Donnellan, Oswald, Baird & Lucas (2006), Psychological Assessment, 18, 192–203
# big5_01   --   I am the life of the party.                               (Extraversion)
# big5_02   --   I sympathize with others’ feelings.                       (Agreeableness)
# big5_03   --   I get chores done right away.                             (Conscientiousness)
# big5_04   --   I have frequent mood swings.                              (Neuroticism)
# big5_05   --   I have a vivid imagination.                               (Intellect / Imagination)
# big5_06   --   I don’t talk a lot.                                       (Extraversion; reverse)
# big5_07   --   I am not interested in other people’s problems.           (Agreeableness; reverse)
# big5_08   --   I often forget to put things back in their proper place.  (Conscientiousness; reverse)
# big5_09   --   I am relaxed most of the time.                            (Neuroticism; reverse)
# big5_10   --   I am not interested in abstract ideas.                    (Intellect / Imagination; reverse)
# big5_11   --   I talk to a lot of different people at parties.           (Extraversion)
# big5_12   --   I feel others’ emotions.                                  (Agreeableness)
# big5_13   --   I like order.                                             (Conscientiousness)
# big5_14   --   I get upset easily.                                       (Neuroticism)
# big5_15   --   I have difficulty understanding abstract ideas.           (Intellect / Imagination; reverse)
# big5_16   --   I keep in the background.                                 (Extraversion; reverse)
# big5_17   --   I am not really interested in others.                     (Agreeableness; reverse)
# big5_18   --   I make a mess of things.                                  (Conscientiousness; reverse)
# big5_19   --   I seldom feel blue.                                       (Neuroticism; reverse)
# big5_20   --   I do not have a good imagination.                         (Intellect / Imagination; reverse)

## IH - Comprehensive Intellectual Humility Scale (CIHS; 22 items, scored 1-5)
# Krumrei-Mancuso & Rouse (2016), Journal of Personality Assessment, 98, 209–221
# ih_01   --   My ideas are usually better than other people’s ideas.                                                         (Lack of intellectual overconfidence; reverse)
# ih_02   --   For the most part, others have more to learn from me than I have to learn from them.                           (Lack of intellectual overconfidence; reverse)
# ih_03   --   When I am really confident in a belief, there is very little chance that belief is wrong.                      (Lack of intellectual overconfidence; reverse)
# ih_04   --   I’d rather rely on my own knowledge about most topics than turn to others for expertise.                       (Lack of intellectual overconfidence; reverse)
# ih_05   --   On important topics, I am not likely to be swayed by the viewpoints of others.                                 (Lack of intellectual overconfidence; reverse)
# ih_06   --   I have at times changed opinions that were important to me, when someone showed me I was wrong.                (Openness to revising one’s viewpoint)
# ih_07   --   I am willing to change my position on an important issue in the face of good reasons.                          (Openness to revising one’s viewpoint)
# ih_08   --   I am open to revising my important beliefs in the face of new information.                                     (Openness to revising one’s viewpoint)
# ih_09   --   I am willing to change my opinions on the basis of compelling reason.                                          (Openness to revising one’s viewpoint)
# ih_10   --   I’m willing to change my mind once it’s made up about an important topic.                                      (Openness to revising one’s viewpoint)
# ih_11   --   I respect that there are ways of making important decisions that are different from the way I make decisions.  (Respect for others’ viewpoints)
# ih_12   --   Listening to perspectives of others seldom changes my important opinions.                                      (Lack of intellectual overconfidence; reverse)
# ih_13   --   I welcome different ways of thinking about important topics.                                                   (Respect for others’ viewpoints)
# ih_14   --   I can have great respect for someone, even when we don’t see eye-to-eye on important topics.                   (Respect for others’ viewpoints)
# ih_15   --   Even when I disagree with others, I can recognize that they have sound points.                                 (Respect for others’ viewpoints)
# ih_16   --   When someone disagrees with ideas that are important to me, it feels as though I’m being attacked.             (Independence of intellect and ego; reverse)
# ih_17   --   When someone contradicts my most important beliefs, it feels like a personal attack.                           (Independence of intellect and ego; reverse)
# ih_18   --   I tend to feel threatened when others disagree with me on topics that are close to my heart.                   (Independence of intellect and ego; reverse)
# ih_19   --   I can respect others, even if I disagree with them in important ways.                                          (Respect for others’ viewpoints)
# ih_20   --   I am willing to hear others out, even if I disagree with them.                                                 (Respect for others’ viewpoints)
# ih_21   --   When someone disagrees with ideas that are important to me, it makes me feel insignificant.                    (Independence of intellect and ego; reverse)
# ih_22   --   I feel small when others disagree with me on topics that are close to my heart.                                (Independence of intellect and ego; reverse)

## LO - Life Orientation Test–Revised (LOT-R; 10 items, scored 1-5)
# Scheier, Carver & Bridges (1994), Journal of Personality and Social Psychology, 67, 1063–1078
# lo_01   --   In uncertain times, I usually expect the best.                (Optimism [LOT-R total])
# lo_02   --   It's easy for me to relax.                                    (Filler — not scored)
# lo_03   --   If something can go wrong for me, it will.                    (Optimism [LOT-R total]; reverse)
# lo_04   --   I'm always optimistic about my future.                        (Optimism [LOT-R total])
# lo_05   --   I enjoy my friends a lot.                                     (Filler — not scored)
# lo_06   --   It's important for me to keep busy.                           (Filler — not scored)
# lo_07   --   I hardly ever expect things to go my way.                     (Optimism [LOT-R total]; reverse)
# lo_08   --   I don't get upset too easily.                                 (Filler — not scored)
# lo_09   --   I rarely count on good things happening to me.                (Optimism [LOT-R total]; reverse)
# lo_10   --   Overall, I expect more good things to happen to me than bad.  (Optimism [LOT-R total])

## BIS - Barratt Impulsiveness Scale (BIS-11; 30 items, scored 1-4)
# Patton, Stanford & Barratt (1995), Journal of Clinical Psychology, 51, 768–774
# bis_01   --   I plan tasks carefully.                               (Nonplanning [Self-control]; reverse)
# bis_02   --   I do things without thinking.                         (Motor)
# bis_03   --   I make-up my mind quickly.                            (Motor)
# bis_04   --   I am happy-go-lucky.                                  (Motor)
# bis_05   --   I don’t “pay attention.”                              (Attentional [Attention])
# bis_06   --   I have “racing” thoughts.                             (Attentional [Cognitive instability])
# bis_07   --   I plan trips well ahead of time.                      (Nonplanning [Self-control]; reverse)
# bis_08   --   I am self controlled.                                 (Nonplanning [Self-control]; reverse)
# bis_09   --   I concentrate easily.                                 (Attentional [Attention]; reverse)
# bis_10   --   I save regularly.                                     (Nonplanning [Cognitive complexity]; reverse)
# bis_11   --   I “squirm” at plays or lectures.                      (Attentional [Attention])
# bis_12   --   I am a careful thinker.                               (Nonplanning [Self-control]; reverse)
# bis_13   --   I plan for job security.                              (Nonplanning [Self-control]; reverse)
# bis_14   --   I say things without thinking.                        (Nonplanning [Self-control])
# bis_15   --   I like to think about complex problems.               (Nonplanning [Cognitive complexity]; reverse)
# bis_16   --   I change jobs.                                        (Motor [Perseverance])
# bis_17   --   I act “on impulse.”                                   (Motor)
# bis_18   --   I get easily bored when solving thought problems.     (Nonplanning [Cognitive complexity])
# bis_19   --   I act on the spur of the moment.                      (Motor)
# bis_20   --   I am a steady thinker.                                (Attentional [Attention]; reverse)
# bis_21   --   I change residences.                                  (Motor [Perseverance])
# bis_22   --   I buy things on impulse.                              (Motor)
# bis_23   --   I can only think about one thing at a time.           (Motor [Perseverance])
# bis_24   --   I change hobbies.                                     (Attentional [Cognitive instability])
# bis_25   --   I spend or charge more than I earn.                   (Motor)
# bis_26   --   I often have extraneous thoughts when thinking.       (Attentional [Cognitive instability])
# bis_27   --   I am more interested in the present than the future.  (Nonplanning [Cognitive complexity])
# bis_28   --   I am restless at the theater or lectures.             (Attentional [Attention])
# bis_29   --   I like puzzles.                                       (Nonplanning [Cognitive complexity]; reverse)
# bis_30   --   I am future oriented.                                 (Motor [Perseverance]; reverse)

## I8 - Impulsive Behavior Short Scale (I-8; 8 items, scored 1-4)
# Kovaleva, Beierlein, Kemper & Rammstedt (2012), GESIS; English-language adaptation validated by Groskurth, Nießen, Rammstedt & Lechner (2022), PLOS ONE, 17(9), e0273801
# i8_01   --   Sometimes I do things impulsively that I should not do.                      (Urgency)
# i8_02   --   I sometimes do things to cheer myself up that I later regret.                (Urgency)
# i8_03   --   I usually think carefully before I act.                                      (Lack of premeditation; reverse)
# i8_04   --   I usually consider things carefully and logically before I make up my mind.  (Lack of premeditation; reverse)
# i8_05   --   I always bring to an end what I have started.                                (Lack of perseverance; reverse)
# i8_06   --   I plan my schedule so that I get everything done on time.                    (Lack of perseverance; reverse)
# i8_07   --   I am willing to take risks.                                                  (Sensation seeking)
# i8_08   --   I am happy to take chances.                                                  (Sensation seeking)

## BSCS - Brief Self-Control Scale (13 items, scored 1-5)
# Tangney, Baumeister & Boone (2004), Journal of Personality, 72, 271–324
# bscs_01   --   I am good at resisting temptation.                                              
# bscs_02   --   I have a hard time breaking bad habits.                                          (reverse)
# bscs_03   --   I am lazy.                                                                       (reverse)
# bscs_04   --   I say inappropriate things.                                                      (reverse)
# bscs_05   --   I do certain things that are bad for me, if they are fun.                        (reverse)
# bscs_06   --   I refuse things that are bad for me.                                             
# bscs_07   --   I wish I had more self-discipline.                                               (reverse)
# bscs_08   --   People would say that I have iron self-discipline.                               
# bscs_09   --   Pleasure and fun sometimes keep me from getting work done.                       (reverse)
# bscs_10   --   I have trouble concentrating.                                                    (reverse)
# bscs_11   --   I am able to work effectively toward long-term goals.                            
# bscs_12   --   Sometimes I can’t stop myself from doing something, even if I know it is wrong.  (reverse)
# bscs_13   --   I often act without thinking through all the alternatives.                       (reverse)

## GRIPS - General Risk Propensity Scale (8 items, scored 1-5)
# Zhang, Highhouse & Nye (2019), Journal of Behavioral Decision Making, 32, 152–167
# grips_01   --   Taking risks makes life more fun                       
# grips_02   --   My friends would say that I'm a risk taker             
# grips_03   --   I enjoy taking risks in most aspects of my life        
# grips_04   --   I would take a risk even if it meant I might get hurt  
# grips_05   --   Taking risks is an important part of my life           
# grips_06   --   I commonly make risky decisions                        
# grips_07   --   I am a believer of taking chances                      
# grips_08   --   I am attracted, rather than scared, by risk            


