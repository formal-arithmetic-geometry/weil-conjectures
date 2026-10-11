## Worker report

The module Sheaf.AlgebraicGeometry.ProjectiveAmpleInvertible states
AlgebraicGeometry.projective_closedImmersion_ample_invertible. Its sole theorem has a sorry
proof; no definitions, extra nodes, dependency replacements or statement corrections are needed.
Local notation expands existing constructions and is not a second definition of any notion.

Hypothesis and clause correspondence:

- A ring A: `(A : Type u) [CommRing A]`, including the zero ring.
- n ≥ 0: `(n : ℕ)`; the homogeneous coordinate index is `ULift.{u} (Fin (n+1))`.
  ULift permits schemes in every universe and retains exactly n+1 coordinates.
- Integral projective space: `Proj.projectiveSpaceOverAffine (Coord n) (ULift ℤ)`, the
  definitional target of `rho n A`; its grading is `Gr n`, the polynomial total-degree grading.
- Projective space over A: `P n A` is the recorded `ProjectiveSpace` applied to Spec A.
  The first projection q is `P n A ↘ Spec (.of A)`, and rho is `ProjectiveSpace.toProjInt`.
- O(1) on the integral model: `O n` expands `Proj.twist (Gr n) 1`, precisely the recorded
  Proj twist, rather than the distinct glued ProjectiveSpace.twist.
- Coordinates T_k: `T n k` evaluates `Proj.unitToTwist (MvPolynomial.isHomogeneous_X ... k)`
  on the global unit function 1. This is the section X_k/1 by `val_unitToTwist_app_top`.
- O(1) over A: `OA n A` is `(tensorPullback (rho n A)).obj (O n)`.
- Scheme X and structural morphism f: explicit `(X : Scheme.{u}) (f : X ⟶ Spec (.of A))`.
- Closed immersion i over Spec A: `(i : X ⟶ P n A) [IsClosedImmersion i]` and
  `hi : i ≫ (P n A ↘ Spec (.of A)) = f`.
- L is the actual twice-pulled module: `L n A i` is `(tensorPullback i).obj (OA n A)`.
- Invertibility: `∃ hL : (L n A i).IsInvertible`; hL supplies the instance argument of the
  subsequent predicate, without assuming the conclusion.
- Absolute ampleness: `@Scheme.Modules.IsAmple X (L n A i) hL` (Stacks 01PS).
- X quasi-compact: `CompactSpace X`, explicitly included even though also in IsAmple.
- Sections s_k: `pb i (OA n A) (pb (rho n A) (O n) (T n k))`, the two canonical section
  maps from the chosen, section-formula-pinned tensor-pullback adjunction units.
- Their non-vanishing loci are affine open subschemes: `∃ U : Coord n → X.Opens` with
  `(U k : Set X) = nonvanishingLocus ... s_k` for every k and `IsAffineOpen (U k)`.
- They cover X: `(⨆ k, U k) = ⊤`.
- The final parenthetical remark about f-ampleness asserts no additional conclusion in
  the node; no relative ampleness predicate is introduced.

Dependency declarations read and used:

- WeilConjectures.AlgebraicGeometry.ProjectiveSpace: `ProjectiveSpace`, `toProjInt`, and
  its canonical over structure (def-nagata-projective-space-base-change).
- WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist: `Proj.twist`,
  `Proj.unitToTwist` (def-weil-pbc-proj-twisting-sheaf); read the full signature and the
  section formula `val_unitToTwist_app_top`.
- Sheaf.AlgebraicGeometry.TensorPullback: `Scheme.Modules.tensorPullback`
  (def-pc-module-pullback), imported through TensorPullbackAdjunction.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`
  (def-weil-closed-immersion's mathlib_match).
- WeilConjectures.AlgebraicGeometry.Modules.Invertible: `Scheme.Modules.IsInvertible`
  (def-sc-invertible-module), imported through Ample.
- Sheaf.AlgebraicGeometry.Ample: `Scheme.Modules.IsAmple`, `nonvanishingLocus`
  (def-weil-pbc-ample-invertible-module).
- Sheaf.AlgebraicGeometry.TensorPullbackAdjunction: `exists_tensorPullbackAdjunction`
  (lem-pc-module-pullback-adjunction). Its unit formula makes `pb` the actual pullback
  of sections, rather than an arbitrary adjunction unit. This is the interface for the
  section pullback already required by def-pc-module-pullback.

Edge cases: n=0 has one coordinate, not an empty coordinate family; its locus covers X.
The zero ring makes Spec A and X empty, and the conclusions remain valid. Empty X is
allowed for every A: invertibility and ampleness are vacuous locally, compactness holds,
and all chart opens can be empty. No Noetherian, field, reducedness, separatedness or
nonemptiness hypothesis is added. All universes and variables are explicitly bound.

Searches:

- msearch.py leanfinder, “A closed immersion into projective space pulls back O(1) to an
  ample invertible sheaf with affine coordinate nonvanishing cover”: 8 hits, all Proj
  affine-chart/morphism primitives, none the asserted theorem.
- msearch.py loogle, `AlgebraicGeometry.ProjectiveSpace, AlgebraicGeometry.Scheme.Modules.IsAmple`:
  no hits; ProjectiveSpace is unknown to the Mathlib-only service.
- msearch.py grep, `IsAmple|ample.*closed|closed.*ample` in AlgebraicGeometry: 0 hits.
- msearch.py leansearch, “closed immersion projective space ample invertible sheaf”:
  service unavailable (Internal Server Error); no absence verdict inferred from it.
- rg in WeilConjectures for ample/Ample under ProjectiveSpace found coordinate-cover
  immersion and descent material, using other twist/section-cover encodings. Read
  CoordinateCoverImmersion and OfAmple interfaces: none states this exact theorem for
  the Proj twist, tensor-formula pullback and recorded absolute IsAmple predicate.
- rg by item id in WeilConjectures and dag/lean_names_upstream.json: no hits.
- rg in lean/Sheaf for IsAmple, closed/ample and tensor-pullback section interfaces:
  found the recorded Ample and TensorPullbackAdjunction modules and useful sibling
  statement conventions; no duplicate of this theorem.

Sources: local literature holds only citation lists on this machine, so read the actual
Stacks pages https://stacks.math.columbia.edu/tag/01PS (definition),
https://stacks.math.columbia.edu/tag/01PU (closed restriction), and
https://stacks.math.columbia.edu/tag/01NG (standard affine covering). These agree with the
node and the five-step proof included in the declaration docstring.
No STATEMENT-DISPUTED or node fault.

## Second reading by J1

I reread the node statement, its source place (Stacks Properties 01PS/01PU and
Constructions 01NF/01NG/01MN), and the complete Lean signature.

- The ring is `A : Type u` with `[CommRing A]`; this includes the zero ring and
  imposes no field, Noetherian, reducedness, or nonemptiness hypothesis. Verdict:
  exact.
- `n : ℕ` represents `n ≥ 0`; `Coord n = ULift.{u} (Fin (n + 1))` gives exactly
  the coordinates `0,…,n`, including the singleton family when `n = 0`. Verdict:
  exact.
- `P n A` is the recorded projective space over `Spec (CommRingCat.of A)`, and
  `rho n A` is its projection to the integral Proj model. `O n` is the recorded
  `Proj.twist` by degree one and `OA n A` is its tensor-formula pullback along
  `rho`. Verdict: exact matches for projective space, `rho`, twisting sheaf, and
  `O(1)` base change.
- `X : Scheme.{u}`, `f : X ⟶ Spec (CommRingCat.of A)`, and
  `i : X ⟶ P n A` with `[IsClosedImmersion i]` and
  `hi : i ≫ (P n A ↘ Spec (.of A)) = f` render the scheme, structure map, closed
  immersion, and compatibility `q ∘ i = f`. Verdict: exact, with no stronger
  geometric hypotheses.
- `L n A i` is the twice-applied `Scheme.Modules.tensorPullback`, hence
  `i^* rho^* O(1)`. The conclusion existentially supplies
  `hL : (L n A i).IsInvertible`, then asserts
  `@Scheme.Modules.IsAmple X (L n A i) hL`; this is exactly absolute ampleness
  of Definition 01PS and does not assume invertibility in advance. Verdict: exact.
- `CompactSpace X` states quasi-compactness as required by 01PS. Verdict: exact
  (redundant with the definitional `IsAmple` conjunction but explicitly present in
  the node).
- `T n k` is the recorded Proj coordinate section, and the nested `pb` terms are
  the canonical tensor-pullback section maps from
  `Classical.choose (exists_tensorPullbackAdjunction ...)`. Thus the displayed
  section is `i^* rho^* T_k`. Verdict: exact; no arbitrary section or private
  pullback notion is introduced.
- The existential `U : Coord n → X.Opens` states, for every `k`, equality with
  `Scheme.Modules.nonvanishingLocus (L n A i) (...)`, `IsAffineOpen (U k)`, and
  `(⨆ k, U k) = ⊤`. These are precisely the affine non-vanishing loci covering
  `X` in the node. Verdict: exact, with quantifier order preserved.

Edge cases checked: `n = 0` has one coordinate; the zero ring and empty schemes
are admitted; empty affine opens and the finite cover remain meaningful. Universe
parameters are explicitly bound and the index type is in the scheme universe.

I searched the source repository, `lean/Sheaf`, Mathlib, and the LeanSearch,
Loogle, LeanFinder, and grep interfaces for an existing theorem or duplicate
notion. The recorded declarations for `ProjectiveSpace`, `Proj.twist`,
`tensorPullback`, `IsClosedImmersion`, `IsInvertible`, `IsAmple`,
`nonvanishingLocus`, and `exists_tensorPullbackAdjunction` are the unique
interfaces used; no existing declaration states this theorem.

No mismatch was found, so no Lean or node statement change was necessary. The
module compiles cleanly with `scompile.py`; its sole proof remains the permitted
`sorry` for this stage, and every declaration docstring carries the source and
`(blueprint: lem-weil-pbc-projective-ample-invertible)`.
