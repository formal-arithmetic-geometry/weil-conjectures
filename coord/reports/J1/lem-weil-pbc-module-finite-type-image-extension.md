## Worker report

The module states the Stacks 01B7 stability result for finite type sheaves of modules. The first conjunct renders an epimorphism `p : F ⟶ G` with `[Epi p]` and `[F.IsFiniteType]` and concludes `G.IsFiniteType`. The second renders an arbitrary morphism `φ : F ⟶ H` with `[F.IsFiniteType]` and concludes finite type of `Abelian.image φ`, matching the image assertion. The third quantifies a `ShortComplex S`; `S.ShortExact` renders the short exact sequence, and finite type hypotheses on `S.X₁` and `S.X₃` conclude finite type of `S.X₂`.

The declaration uses Mathlib's `SheafOfModules.IsFiniteType`, `CategoryTheory.ShortComplex.ShortExact`, and `CategoryTheory.Abelian.image`, with `moduleRings X` from `Sheaf.Paper.DerivedHomMayerVietoris`. The proof is intentionally `sorry` for stage 2.

Dependencies used: `def-pc-scheme` via Mathlib's `AlgebraicGeometry.Scheme` background; `def-weil-sheaf-of-modules-category` via `SheafOfModules`; `def-weil-pbc-module-finite-type-presentation` via `SheafOfModules.IsFiniteType`; `pqf-def-coherent` is not unfolded because the statement explicitly uses the ringed-space finite-type notion; `def-weil-pbc-exact-sequence` via `ShortComplex.ShortExact`.

Edge cases checked: finite generating index zero is allowed by Mathlib's finite-type class; empty schemes and zero sheaves are covered; short exact sequences are represented by `ShortExact`, including zero end terms; no independent index universe is introduced.

Searches: `msearch.py leanfinder` for finite type images/extensions (found only definitions); `msearch.py loogle` for `SheafOfModules.IsFiniteType, CategoryTheory.Epi` (no result); `msearch.py grep` for finite-type epi/extension lemmas (only generator definitions and `ofEpi` instance); `rg` in `WeilConjectures` and `lean/Sheaf` (no existing theorem with this node id or statement). Mathlib's existing definitions do not state either stability theorem.
## Second reading by J1

The node introduces a ringed space `(X, O_X)`, its sheaf-of-modules category, and finite type modules. Lean renders these as `X : RingedSpace.{u}` and `SheafOfModules.{u} (moduleRings X)`; `SheafOfModules.IsFiniteType` is the recorded Mathlib realization of the dependency definition (local finite generators), with no extra scheme, Noetherian, or finiteness assumptions.

The first conclusion clause is the universal statement over `F G` and `p : F ⟶ G`, with instance hypotheses `[Epi p]` and `[F.IsFiniteType]`, concluding `G.IsFiniteType`. The second is over arbitrary `φ : F ⟶ H`, assumes `[F.IsFiniteType]`, and concludes `(Abelian.image φ).IsFiniteType`, which is the node's image `Im φ` in the abelian module category. The third universally quantifies `S : ShortComplex (SheafOfModules ...)`, assumes `S.ShortExact`, `[S.X₁.IsFiniteType]`, and `[S.X₃.IsFiniteType]`, and concludes `S.X₂.IsFiniteType`; this exactly represents the stated short exact extension. Conjunct order and quantifier order agree with the node.

Edge cases were checked: `n = 0` is permitted by Mathlib's finite index type, so zero modules and empty generating families are included; zero terms in a short exact sequence are allowed; an empty space and arbitrary characteristic are not excluded; and the only universe is the common `u` for the ringed space and sheaves, with no independent index universe. The instance binders are hypotheses, not added mathematical conditions.

I searched Mathlib and both the slopmaster2 source and repository with LeanFinder/Loogle/grep for finite-type image and extension theorems and for `finiteType_image_extension`; only the `SheafOfModules.IsFiniteType` definition and generator transport instance exist. No existing declaration states this node. The module compiled cleanly with `scompile.py`. No mismatch was found, so no source or node correction was needed.
