# A1

Case: Slow Derived Tensor  
Variant: ordinary `def`, same body  
Commit/toolchain: control shape from `428569e1ce1`, Lean v4.33.1  
Operation: same final conversion  
Representation: regular definition hint; no body or consumer change  
Result: fast control family; standalone ordinary-def timing was not retained in the historical log  
Interpretation: declaration-kind matrix separates regular hint from `abbrev`; do not treat this row as a new mathematical proof  
Confidence: source-level control confirmed, exact standalone timing incomplete

The fast-control wording above is historical. Round two measured an actual compile failure;
see `A1-round2.md` and `probes/round2/A1.lean`.
