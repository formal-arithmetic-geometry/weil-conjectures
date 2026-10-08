+++
id = "rem-sf-orientation-pointer"
kind = "remark"
title = "Where the orientation is constructed"
order = 2048
uses = ["def-sf-orientation"]
+++
The orientation datum of [def-sf-orientation] is not assumed: it is
constructed in the purity chapter that precedes this one, where the relative
product theorem [thm-sf-kunneth-relative] proved above supplies the
relative input that the purity chapter's pending notes declare missing.
Concretely, the affine-line orientation over an arbitrary base, the
affine-space case, the Gysin sheaf/group identification, the frame
transformation law, purity for vector bundles and smooth purity are proved
there; the reader should read the purity chapter immediately after this one,
the consequences *Perfectness of the trace–cup pairing* and *The trace isomorphism* are stated
conditionally on [def-sf-orientation] precisely so that they do not
depend on the order in which the two chapters are read, while
[thm-sf-dual-perfect] takes its case $f=a_X$ directly from the smooth
dualizing-complex identification of the purity chapter.
