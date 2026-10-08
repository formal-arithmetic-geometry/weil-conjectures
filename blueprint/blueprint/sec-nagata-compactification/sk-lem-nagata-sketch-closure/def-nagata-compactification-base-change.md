+++
id = "def-nagata-compactification-base-change"
kind = "definition"
title = "Base-change construction for a compactification"
order = 75
lean = ["AlgebraicGeometry.Compactification.baseChange", "AlgebraicGeometry.Compactification.ofIsPullback"]
uses = ["def-nagata-compactification"]
+++
Given a compactification $C=(X\to\overline X\to S)$ and $S'\to S$, define
$C_{S'}$ to be

$$
X\times_SS'\longrightarrow\overline X\times_SS'\longrightarrow S'.
$$
