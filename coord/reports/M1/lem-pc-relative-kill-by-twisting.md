## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeSerreVanishing` states
`AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_tensorPow_of_relatively_ample`.
Its sole theorem has proof `by sorry`; it defines no new notion. The node is unchanged except
for `lean`. The server single-file compile succeeded in 2.4 seconds with no warnings or errors.

Hypothesis and conclusion correspondence:

- Schemes X and S: `{X S : Scheme.{u}}`, with arbitrary explicit universe `u`.
- S Noetherian: `[IsNoetherian S]`, Mathlib's locally Noetherian plus quasi-compact class.
  The dependency `pqf-def-locnoeth` supplies the locally Noetherian notion, but the item
  explicitly says Noetherian; using only `[IsLocallyNoetherian S]` would omit quasi-compactness.
- Proper morphism f: `(f : X ⟶ S) [IsProper f]`, the convention node's named Mathlib notion.
- F an O_X-module: `(F : X.Modules)`.
- F quasi-coherent: `[F.IsQuasicoherent]`, Mathlib's `SheafOfModules.IsQuasicoherent`.
- F coherent: `hF : RingedSpace.IsCoherent X.toRingedSpace F`, the recorded definition
  of `pqf-def-coherent`, using exactly the same module carrier as `X.Modules`.
- L invertible: `(L : X.Modules) [L.IsInvertible]`, the recorded scheme-module class.
- For every affine open V of S, L restricted to f inverse V is ample: `hL` quantifies over
  every `V : S.Opens` with `IsAffineOpen V`, and uses `IsAmple (f ⁻¹ᵁ V).toScheme` on
  `L.restrict (f ⁻¹ᵁ V).ι`. This is actual restriction along the open inclusion, not
  an arbitrary map and not a module pullback. `∃ h : ...IsInvertible` supplies the Prop-valued
  instance required by the existing `IsAmple` definition; restriction of an invertible
  module is invertible, so it adds no hypothesis. In particular there is no chosen affine
  cover substituted for the universal affine-open condition.
- Existence of a threshold: `∃ n₀ : ℕ`. Tensor powers in the recorded ampleness dependency
  are defined for nonnegative n, with power zero the structure module. An eventual integer
  threshold on these n is equivalent to a nonnegative threshold (replace an integer bound
  by its maximum with zero); thus this does not exclude any twisting case of the node.
- Every sufficiently large n: `∀ n : ℕ, n₀ ≤ n →`.
- Every positive degree p, with the same threshold: `∀ p : ℕ, 0 < p →` after the n quantifier.
- Vanishing of R^p f_*(F tensor L^n):
  `IsZero ((higherDirectImage f p).obj (F ⊗ L.tensorPow n))` in S.Modules.
  The existing higherDirectImage is the right derived functor of module pushforward,
  rather than cohomology of an underlying abelian sheaf. The local `letI` obtains
  EnoughInjectives from the recorded ringed-space enough-injectives theorem. The canonical
  Mathlib Abelian instance is retained, and injective resolutions follow from EnoughInjectives;
  no existence hypothesis is imposed on the geometric data.

Dependency declarations read and used:

- `def-pc-morphism-conventions` is an explicit convention record (no declaration or module);
  it points to Mathlib morphism properties. Here use `AlgebraicGeometry.IsProper` from
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` (separated, universally closed, locally finite type).
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian` from
  `Mathlib.AlgebraicGeometry.Noetherian`; `[IsNoetherian S]` extends it and CompactSpace.
- `pqf-def-coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `Sheaf.AlgebraicGeometry.Coherent`, and the same module's documented Mathlib
  `SheafOfModules.IsQuasicoherent`.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible` from
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible` (imported through Ample).
- `def-weil-pbc-ample-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsAmple`
  from `Sheaf.AlgebraicGeometry.Ample`, with the existing `Scheme.Modules.tensorPow`.
- Supporting existing APIs: `Scheme.Modules.restrict` from
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`; `Scheme.Modules.higherDirectImage` from
  `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage` (full definition read);
  `RingedSpace.moduleSheaves_abelian_enoughInjectives` from
  `Sheaf.Topology.RingedSpaceModuleEnoughInjectives`.

Edge cases checked: no nonempty scheme or base condition; the empty base and its empty
finite cover allow threshold zero. The zero coherent module is allowed. Degree p=0 is
excluded explicitly; power n=0 is allowed if the bound is zero and denotes O_X. No flatness,
projectivity, base field, characteristic, relative dimension, or geometric connectedness
assumption was added. Universes are explicitly bound and no auto-bound implicit is used.
The proof docstring records all four DAG proof steps, including their supporting nodes.

Searches, via `/home/ubuntu/weil-launcher/msearch.py M1 lem-pc-relative-kill-by-twisting`:

- `leanfinder`, query "Relative Serre vanishing higher direct images of coherent module
  twisted by relatively ample invertible module": 8 hits, on derived-category support
  and injective/projective single-complex morphisms; none is relative Serre vanishing.
- `loogle`, query `AlgebraicGeometry.IsProper, AlgebraicGeometry.IsLocallyNoetherian`:
  0 hits.
- `grep`, query `Serre|kill_by_twisting|relatively ample`, subdirectory `AlgebraicGeometry`:
  0 Mathlib hits.
- `leansearch`, query "relative Serre vanishing for proper morphism coherent module ample
  invertible sheaf": unavailable, Internal Server Error; no mathematical verdict inferred.
- `rg` over source `WeilConjectures/AlgebraicGeometry` for Serre, higherDirectImage,
  tensorPower: found absolute vanishing over a field in Cohomology/Serre.lean and the
  higher-direct-image API in Cohomology/DirectImage.lean, but no exact theorem.
- `rg` for the item id in `WeilConjectures`: no hits.
- `rg` for `relative.*Serre|relatively.*ample` and the proposed declaration in
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no hits.
- `rg` over `lean/Sheaf/AlgebraicGeometry` for Serre, vanishing, and tensorPow:
  ampleness lemmas, unrelated vanishing, and tensor-power APIs; no matching statement.

Source checked at https://stacks.math.columbia.edu/tag/02O1 (the local literature checkout
has no coherent.tex). It gives precisely this proper/Noetherian/coherent/relatively ample
vanishing and finite-affine-cover proof. Source metadata fault: Tag 02O1 currently has
number 30.16.2, not the node's "30.17.1"; the stable tag and label are correct. This does
not affect the statement, so source metadata was not edited. No STATEMENT-DISPUTED issue,
new definition node, or unusable dependency was found.


## Second reading by M1

I independently opened the node copy and RelativeSerreVanishing.lean, all five
statement-dependency nodes, and the declarations they record. The following is my
object/hypothesis/conclusion checklist; every entry passes.

- Schemes X and S: `{X S : Scheme.{u}}`; these are arbitrary schemes, with `u`
  explicitly declared. There is no field, characteristic, dimension or nonemptiness binder.
- S Noetherian: `[IsNoetherian S]`. I opened Mathlib.AlgebraicGeometry.Noetherian:
  this extends `IsLocallyNoetherian S` and `CompactSpace S`. This is precisely the
  Noetherian hypothesis in this item, rather than only the weaker notion named by
  pqf-def-locnoeth. Its locally Noetherian class requires Noetherian sections on affine opens.
- Proper f:X -> S: `(f : X ⟶ S) [IsProper f]`. The convention dependency points to
  Mathlib's morphism properties; I opened Morphisms.Proper and checked the separated,
  universally closed and locally finite type fields. Properness supplies quasi-compactness.
- F an O_X-module: `(F : X.Modules)`, the actual module-sheaf category.
- F quasi-coherent: `[F.IsQuasicoherent]`. I opened Mathlib's Quasicoherent module:
  its class is local presentation as a cokernel of a map of free module sheaves,
  the same notion as the node's affine-local description on a scheme.
- F coherent: `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`. I opened
  Sheaf.AlgebraicGeometry.Coherent: finite type plus finite-type kernels for every
  map from a finite free module on every open, on the same carrier as X.Modules.
- L invertible: `(L : X.Modules) [L.IsInvertible]`. I opened the recorded
  WeilConjectures.AlgebraicGeometry.Modules.Invertible class: locally isomorphic
  to the structure module. No competing SheafOfModules invertibility predicate is used.
- Ampleness on every affine inverse image: `hL : ∀ V : S.Opens, IsAffineOpen V → ...`.
  The object is exactly `L.restrict (f ⁻¹ᵁ V).ι` on `(f ⁻¹ᵁ V).toScheme`.
  I opened Mathlib's restrictFunctor/restrict: this is restriction along an open
  immersion, with restrictFunctorIsoPullback identifying it with the open pullback.
  Thus the existing invertible-pullback instance and invariance under isomorphism
  show the existential invertibility witness in hL adds no condition.
  I opened Sheaf.AlgebraicGeometry.Ample: `IsAmple` is quasi-compactness plus an
  affine nonvanishing neighbourhood of each point from a positive tensor-power
  section, exactly the recorded absolute ampleness notion. It is not upstream's
  different field/projective definition `AlgebraicGeometry.IsAmple`.
- A single threshold: `∃ n₀ : ℕ`; the node's eventual integer bound is equivalent
  after raising it to max(n₀,0), since this dependency defines powers for n >= 0.
  An arbitrary lower integer bound never requires asserting negative twists:
  an equally valid nonnegative witness may always be chosen.
- Every sufficiently large twist: `∀ n : ℕ, n₀ ≤ n →`, following the existential.
- Every positive degree with that same threshold: `∀ p : ℕ, 0 < p →`, following n.
  The bound is uniform in p, not a separate bound for each degree.
- Vanishing: `IsZero ((higherDirectImage f p).obj (F ⊗ L.tensorPow n))` in S.Modules.
  I opened the definition in Cohomology.DirectImage: it is `(pushforward f).rightDerived p`.
  The tensor and tensorPow definitions in Modules.Invertible use the O_X-module
  monoidal structure, and tensorPow 0 is its unit. These are module higher direct
  images, not the abelian-sheaf cohomology H used by some upstream statements.
- Derived-functor infrastructure: the `letI : EnoughInjectives X.Modules` comes
  from the second clause of the named ringed-space enough-injectives theorem,
  whose signature and docstring I opened. This supplies injective resolutions
  without assuming a new geometric hypothesis or choosing a different Abelian instance.

Source reading: the local Stacks checkout is absent on this machine. I read the
actual coherent.tex at
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex,
label lemma-kill-by-twisting, and the rendered stable tag
https://stacks.math.columbia.edu/tag/02O1. The source introduces exactly these
schemes, morphism and modules, with the same four hypotheses and uniform vanishing
conclusion; there is no standing field assumption. I also read morphisms.tex,
labels definition-relatively-ample and lemma-finite-type-over-affine-ample-very-ample.
The former defines relative ampleness by quasi-compactness of f and ampleness on
EVERY affine inverse image. The first condition is supplied here by properness.
The current numerical lemma label differs from the node's number, as the first
worker reported; the tag and TeX label identify the correct source. No node
statement correction is present or needed.

Edge cases: empty S and X are admitted, and no nonempty affine index is assumed;
for an empty finite cover the proof's threshold can be zero. F=0 is admitted.
The twist n=0 is allowed if the eventual threshold permits it and denotes O_X;
p=0 is deliberately excluded. There is no restriction on characteristic, no
flatness or projectivity hypothesis, and no independent small test-object universe
that could make hL vacuous. All schemes and their module categories use explicit u;
any pair of sizes can be accommodated in a common larger universe. The section has
no unbound variable or universe.

Independent searches (recorded by msearch.py in searches.jsonl):

- LeanFinder: "Vanishing of derived pushforward after tensoring coherent sheaves
  with large powers of a line bundle": eight hits, unrelated derived-category
  single-object/Tor results and general scheme lemmas; no exact match.
- Loogle: `AlgebraicGeometry.IsProper, CategoryTheory.Limits.IsZero`: zero hits.
  A prior query for `AlgebraicGeometry.Scheme.Modules.tensorPow` reported an
  unknown identifier, which is not evidence of absence.
- LeanSearch: "higher direct image vanishes for sufficiently positive twists of
  an ample line bundle": service Internal Server Error, recorded as unavailable,
  with no mathematical verdict inferred.
- msearch grep: `higherDirectImage|ample.*vanish|vanish.*ample`: one unrelated
  arithmetic-function documentation hit. Direct rg over Mathlib/AlgebraicGeometry,
  WeilConjectures/AlgebraicGeometry and lean/Sheaf/AlgebraicGeometry for
  `Serre|[Rr]elative.*[Vv]anishing|higherDirectImage.*tensorPow|02O1|kill.by.twisting`
  found only upstream absolute Serre vanishing and unrelated material.
  I opened the upstream exists_subsingleton_H_tensorObj_tensorPow signature:
  it is over a field and uses a different ampleness predicate and abelian-sheaf H,
  so is not this statement. A further rg of dag/lean_names_upstream.json,
  WeilConjectures and lean/Sheaf for relative ampleness, the item id and
  tensor/higherDirectImage combinations found only the projection formula,
  not this statement. No exact existing declaration was found.

Delivery review: there are no new definition nodes or dependency modules to review.
The module defines no notion and has exactly one named theorem, with `by sorry`.
The module and theorem docstrings name Tag 02O1 and the blueprint id; all four
node proof steps, including their supporting nodes, are present in order.
All imports serve the signature or its infrastructure, and line lengths satisfy
100 columns. The node's lean.statement agrees verbatim after whitespace
normalization with the declaration signature, including the local instance binder.

Mismatches found: none. Changes: appended this independent reading to report.md;
the Lean module and node record are unchanged. The server single-file compile and
stage-2 delivery preflight are checked before the push.
