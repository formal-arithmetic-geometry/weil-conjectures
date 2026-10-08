+++
id = "def-amb-vector-integration"
kind = "definition"
title = "Integration along a vector bundle"
order = 1972
uses = ["def-asd-vector-bundle-zero-section", "def-coefficient-twists-detailed", "lem-amb-affine-space-top-trace", "lem-amb-linear-trace-invariance"]
+++
Let $\pi:E\to S$ be a vector bundle of constant
rank $d$, in the sense of
[def-asd-vector-bundle-zero-section]. Its integration
map

$$
t_\pi:R\pi_!A_E(d)[2d]\longrightarrow A_S
$$

is the map which on a trivializing open set is the
affine-space integration of
[lem-amb-affine-space-top-trace]. These maps glue
as morphisms of sheaves: the source has cohomology
only in degree zero on a trivializing cover, and
[lem-amb-linear-trace-invariance] identifies the
maps on every overlap.
The notation refers to Tate twists.
