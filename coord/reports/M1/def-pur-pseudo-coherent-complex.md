## Worker report

Module `Sheaf.AlgebraicGeometry.PseudoCoherentComplex` defines
`AlgebraicGeometry.Scheme.IsPseudoCoherent`. This is a complete Prop-valued definition,
with no theorem, proof obligation, or sorry. No new nodes or dependency modules are needed.

Clause-by-clause correspondence:

- A scheme Y: `(Y : Scheme.{u})`, the declaration of def-pc-scheme.
- An object E of D(O_Y): `(E : schemeDerivedCategory Y)`, using the recorded
  declaration of def-pc-derived-category. Its shared HasDerivedCategory binder is retained.
- Locally on Y: `∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ ...`. This is an open neighbourhood
  of every point, equivalently an open cover; it does not require Y to be affine or
  quasi-compact.
- A complex of O_U-modules: `P : CochainComplex (SheafOfModules.{u}
  ((moduleRings Y.toRingedSpace).over U)) ℤ`. The localized site of opens contained
  in U describes sheaves on U. The family of HasDerivedCategory binders on these
  localized categories supplies their localizations, not a geometric hypothesis.
- Bounded above: `∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i)`. In an additive category,
  IsZero is the invariant formulation of a zero term. There is no lower bound.
- Finite free terms: `∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
  (R := (moduleRings Y.toRingedSpace).over U) (ULift.{u} (Fin r)))`.
  This is an actual finite free sheaf, not just a locally free sheaf or a finite type
  sheaf. Rank is allowed to vary with degree; neither ranks nor upper bounds are uniform
  across neighbourhoods.
- Quasi-isomorphic locally: `Nonempty ((SheafOfModules.overFunctor ... U)
  .mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P)`.
  Isomorphism in the localization at quasi-isomorphisms is the derived-object form of
  being quasi-isomorphic, and does not demand a particular direction of a chain map.
- The parenthetical all-m condition is the equivalent characterization cited by the
  node, not an additional conjunct: the definition uses its primary bounded-above
  finite-free characterization. On schemes this follows from quasi-coherent cohomology
  (08E5), the affine comparison (08E7), and the ring pseudo-coherent characterization.
  No theorem asserting that equivalence is introduced during this statement-only stage.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`, the locally affine
  locally ringed space structure, and `Scheme.Hom` (the latter does not occur in this def).
- `Sheaf.AlgebraicGeometry.DerivedCategory`, `AlgebraicGeometry.schemeDerivedCategory`:
  DerivedCategory of the shared `SheafOfModules (moduleRings Y.toRingedSpace)` category.
- Through that module's imports, `AlgebraicGeometry.moduleRings` and the existing
  `moduleOverFunctor_additive`, `moduleOverFunctor_limits`, `moduleOverFunctor_colimits`
  instances from `Sheaf.Paper.DerivedHomMayerVietoris` provide exact derived restriction.
- Mathlib `SheafOfModules.overFunctor`, `SheafOfModules.free`, `DerivedCategory.Q`,
  and `Functor.mapDerivedCategory` are used without copies of any notion.

Edge cases checked before writing: the empty scheme satisfies the pointwise local
condition vacuously, as an empty covering should. Zero terms and rank zero are allowed
by `Fin 0`; the zero complex therefore qualifies on every neighbourhood. An unbounded
negative tail is allowed. Y can be disconnected and non-quasi-compact: the neighbourhood,
upper bound, and ranks may all vary. No Noetherian, affine, separated, characteristic,
or quasi-coherent hypothesis is added. Universe u matches the shared module carrier;
ULift permits the finite basis in Type u, including u = 0. Universe w is shared by
all derived categories used in the restriction.

Searches for an existing definition:

- msearch.py leanfinder: “An object of the derived category of sheaves of modules on
  a scheme is pseudo-coherent if locally quasi-isomorphic to a bounded above complex
  of finite free modules”. Eight hits: quasi-coherent/finite-type sheaves and generic
  derived T-structure facts; no exact definition.
- msearch.py loogle: `SheafOfModules.free, DerivedCategory.Q`. Zero hits.
- msearch.py grep: `pseudo.?coherent|PseudoCoherent`. Zero Mathlib hits.
- msearch.py leansearch: `pseudo coherent derived category scheme locally bounded above
  finite free complex`. Service unavailable (Internal Server Error), recorded by the tool.
- rg on WeilConjectures and lean/Sheaf: `pseudo.?coherent|PseudoCoherent|finiteFree|FiniteFree`.
  The source has bounded finite-free complexes for direct images, not this definition.
  Sheaf has ring-specific `DerivedCategory.IsPseudoCoherent` and related lemmas;
  their carrier is ModuleCat of a ring, not sheaves on a scheme. It also has finite-free
  Hom lemmas using exactly the free sheaf encoding reused here.
- rg of dag/lean_names_upstream.json and WeilConjectures for the node id and
  `IsPseudoCoherent`: no source declaration. No full-name clash with
  `AlgebraicGeometry.Scheme.IsPseudoCoherent`.

Source inspection: read Stacks https://stacks.math.columbia.edu/tag/08CB,
https://stacks.math.columbia.edu/tag/08E5, and
https://stacks.math.columbia.edu/tag/08E7 (local Stacks checkout is absent).
Node source-field fault: it still says perfect.tex Tags 08FT/08G5, whereas its statement
and reviewed note identify 08CB/08E5/08E7 correctly. The module follows the statement's
correct references; the source field is left unchanged under the delivery field rules.
This does not require changing the mathematical statement. No STATEMENT-DISPUTED issue.

## Second reading by M1

I independently matched the node's objects, hypotheses, and conclusion against
`AlgebraicGeometry.Scheme.IsPseudoCoherent` in
`lean/Sheaf/AlgebraicGeometry/PseudoCoherentComplex.lean`.

- The scheme `Y` is rendered by `(Y : Scheme.{u})`, using Mathlib's scheme.
- The derived object `E` is rendered by `(E : schemeDerivedCategory Y)`, with the
  shared `[HasDerivedCategory.{w} (SheafOfModules (moduleRings Y.toRingedSpace))]`
  instance required by the dependency definition.
- “Locally on `Y`” is exactly `∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ ...`.
- The local complex of `O_U`-modules is
  `P : CochainComplex (SheafOfModules ((moduleRings Y.toRingedSpace).over U)) ℤ`.
  Its derived category is supplied by the explicit family of localized
  `HasDerivedCategory` instances, which is necessary to type `Q.obj P` and the
  restriction's `mapDerivedCategory`.
- Bounded above is `∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i)`.
- Finite free terms are expressed as
  `∀ i, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free (Fin r))`; this is the
  categorical finite-coproduct-of-unit formulation and permits rank zero and
  degree-dependent ranks.
- Local quasi-isomorphism is the derived-category isomorphism
  `Nonempty (overFunctor U |>.mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P)`.
  An isomorphism correctly expresses quasi-isomorphism without choosing a chain-map
  direction.

The node's parenthetical “equivalently, m-pseudo-coherent for every m” is explanatory
and is not an extra conjunct; the primary local characterization is the one defined.
No extra geometric hypothesis (Noetherian, affine, separated, finite type,
quasi-coherent, or characteristic) occurs. The empty scheme is vacuous; zero terms
and `Fin 0` are allowed; negative unbounded tails are allowed; neighborhoods and
ranks may vary. Universes `u` and shared derived-category universe `w` do not exclude
these cases.

I searched Mathlib and the source checkout with LeanSearch, Loogle/LeanFinder, and
`rg` for pseudo-coherent complexes and `IsPseudoCoherent`. Only the ring-specific
`DerivedCategory.IsPseudoCoherent` and generic finite-free results occur; no exact
scheme-level declaration exists. The existing dependency declarations
`AlgebraicGeometry.schemeDerivedCategory` and Mathlib's `SheafOfModules.free`,
`overFunctor`, and `DerivedCategory.Q` are the declarations used here. The source
place in the node metadata still names the old `perfect.tex` tags, while the worker's
reviewed statement and docstring correctly use Stacks 08CB, 08E5, and 08E7; the
statement itself needs no change, and delivery rules permit changing only `lean`.

No mismatch was found in the Lean statement, so no code or node statement was changed
in this second reading. The module compiles cleanly with `scompile.py`.
