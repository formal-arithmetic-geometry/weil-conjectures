# Diagonal completed trace pullback rework

The stale rework was an import-resolution failure for the diagonal coefficient modules. Their
current public imports resolve. The delivered source only changes the proof script of
`completedRealization_shiftedLine_isIso`, replacing selective simplification with direct unfolding
before the existing instance proof; all declarations and signatures are unchanged.
