## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeAssassinBaseChange` states
`AlgebraicGeometry.Scheme.Modules.relativeAssassin_baseChange_iff`, with `sorry` as its
entire proof. It constructs no new notion. The source is Stacks Project, Divisors,
Tag 05DC (`lemma-base-change-relative-assassin`), read in
`literature/stacks-project/divisors.tex`, including both proof paragraphs.
The declaration docstring reproduces all nine proof steps and their dependency references.

Clause-by-clause correspondence:

- Schemes X, S, S': `{X S S' : Scheme.{u}}`, with explicit universe `u`.
- Locally finite type morphism f: `(f : X ⟶ S) [LocallyOfFiniteType f]`.
  There is no quasi-compactness or flatness hypothesis.
- Arbitrary quasi-coherent O_X-module: `(F : X.Modules) [F.IsQuasicoherent]`.
  In particular, neither finite type nor finite presentation of F is assumed.
- Arbitrary base morphism: `(g : S' ⟶ S)` with no condition on g.
- X' = X ×_S S': `Limits.pullback f g`; its projections g' and f' are respectively
  `Limits.pullback.fst f g` and `Limits.pullback.snd f g`.
- Arbitrary point of the base change: `(z' : ↑(Limits.pullback f g))`.
  The image z is `Limits.pullback.fst f g z'`; r' is `Limits.pullback.snd f g z'`;
  r is `f (Limits.pullback.fst f g z')`. They are images, not extra point hypotheses.
- F' = (g')*F: `((tensorPullback (Limits.pullback.fst f g)).obj F)`.
  This uses the explicit tensor pullback from the recorded dependency.
- Relative association on X'/S': membership of z' in
  `relativeAssassin (Limits.pullback.snd f g)` of that pullback module.
- Relative association on X/S: membership of the first projection of z' in
  `relativeAssassin f F`.
- In both occurrences, the already landed `Scheme.Modules.relativeAssassin` takes the
  tensor pullback to the fibre, evaluates at `f.asFiber`, and tests its stalk with
  `Scheme.Modules.associatedPoints`. That definition tests whether the stalk ring's
  maximal ideal belongs to `RingTheory.annihilatorAssociatedPrimes` of the module stalk.
  The chosen element is necessarily nonzero: the annihilator of zero is the unit ideal,
  whereas the maximal ideal is prime and proper. No Noetherian premise enters this test.
- Residual fibre Spec(κ(r') ⊗_[κ(r)] κ(z)):
  `Spec (Scheme.Pullback.Triplet.ofPoint ((pullbackSymmetry f g).hom z')).tensor`.
  The canonical pullback symmetry sends z' to the same point with the two projections
  interchanged. The triplet's x is r', y is z, and s is r. Its tensor is the pushout of
  the actual induced residue-field homomorphisms in CommRingCat. This is the usual
  commutative algebra tensor product, including (a⊗b)(c⊗d)=ac⊗bd; it is not a new
  tensor construction or an arbitrary coefficient map.
- The point corresponding to z' in that residual spectrum is exactly
  `Scheme.Pullback.SpecOfPoint ((pullbackSymmetry f g).hom z')`.
  Mathlib defines this by the residue-field tensor map to κ(z') and the unique point
  of Spec κ(z'); `SpecTensorTo_SpecOfPoint` recovers the original pullback point.
- Generic point of an irreducible component: `∃ Z ∈ irreducibleComponents (...),
  IsGenericPoint (...) Z`. Here components are maximal irreducible subsets, and
  `IsGenericPoint p Z` means closure {p} = Z. The spectrum above is precisely the
  residual fibre of the map of fibres used in the node.
- Both directions and both conditions are retained by `↔` and `∧`.

Dependency declarations read and used (directly or through their recorded interface):

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: imports the recorded quasi-coherence
  and finite-type notions. Only Mathlib's `SheafOfModules.IsQuasicoherent` is used here;
  the dependency's stronger `IsQuasiCoherentFiniteType` is deliberately not assumed.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the documented scheme
  base change is `Limits.pullback`, with its two projections; `moduleBaseChange`
  is the convention for module base change along a morphism of over-schemes.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: reexports
  `Scheme.Modules.tensorPullback` from `WeilConjectures.AlgebraicGeometry.TensorPullback`.
  Its normalized adjunction/composition interface is available for the proof.
- `WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes`:
  `RingTheory.annihilatorAssociatedPrimes`, used by the existing associated-point definition.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`; the associated-point definition uses the same
  stalks bundled by `RingedSpace.moduleStalkFunctor` from the existing module-stalk API.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`, `asFiber`, used by
  the existing relative-assassin definition.
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` (mathlib_match, no lean record needed).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`; the algebra tensor is
  the canonical CommRingCat pushout used by Mathlib's `Triplet.tensor`.
- `Sheaf.AlgebraicGeometry.RelativeAssassin`: `Scheme.Modules.relativeAssassin` and
  `associatedPoints`. This already landed node, `def-trf-relative-assassin`, has been
  added to stmt_deps as authorized by brief-stage2 §5. No private copy is introduced.
- `Mathlib.AlgebraicGeometry.PullbackCarrier`: `Scheme.Pullback.Triplet.ofPoint`,
  `Triplet.tensor`, `SpecOfPoint`, and the canonical-map characterization described above.

All recorded proof-dependency modules are imported without `public` when they are not
already statement imports, including Flat, Noetherian, Modules.Tilde,
FibrePrimesResidueFields, Pullbacks, IntermediateField.Adjoin.Algebra, AffineScheme,
AssociatedPrimeMinimalOfDepth, Localization.AtPrime.Basic,
Ideal.AssociatedPrime.Localization, and KrullDimension.Basic.
`lem-trf-flat-pullback-associated-points` and `lem-trf-tensor-fields-cohen-macaulay`
had no recorded Lean declaration or mathlib_match when inspected; no import was invented
for those proof-only nodes.

Edge cases checked mathematically before writing:

- Empty total/base-changed scheme: quantification over z' is empty, as in the source.
- Zero module: both relative assassins are empty, so the equivalence remains valid.
- Identity and arbitrary base change are included; neither g nor S is restricted.
- Nonclosed z is included. κ(z)/κ(r) is finitely generated as a field, not necessarily
  finite as an algebra. No incorrect algebra-finite-type hypothesis was inserted.
- Purely inseparable extensions can yield nonreduced tensor spectra; the statement uses
  generic points of irreducible components, not reducedness or separability.
- A nongeneric prime such as the diagonal in k(t)⊗_k k(u) is excluded by the component
  genericity condition, which is therefore not dropped.
- Arbitrary quasi-coherent modules, including infinitely generated ones, remain included.
- All schemes and module carriers use the shared arbitrary universe u of the project's
  Scheme.Modules API; there is no independent smaller test-object universe.

Searches performed for an existing exact statement:

- msearch.py leanfinder, query: "Relative associated points of a quasi coherent module under
  arbitrary scheme base change characterized by generic points of residual fibres".
  Eight hits, including fibreToSpecResidueField_apply, SpecMap_residue_apply,
  Flat.generalizingMap and genericPoint_eq_of_isOpenImmersion; none states this equivalence.
- msearch.py loogle, query: "associatedPrimes, TensorProduct". Zero hits.
- msearch.py grep, query:
  "relativeAss|assassin|associated.*base.change|base.change.*associated".
  Two unrelated category/site base-change-natural-transformation hits; no exact statement.
- msearch.py leansearch, query: "Relative associated points of a quasi coherent sheaf after
  arbitrary base change are generic points of the residual tensor fibre over relative
  associated points". Eight hits, including Module.rankAtStalk_baseChange,
  Algebra.QuasiFiniteAt.baseChange and Scheme.Pullback.ofPointTensor_SpecTensorTo;
  none states association under base change. The last supplied the canonical point API.
- rg of WeilConjectures and lean/Sheaf for relativeAss/relative_ass/RelativeAss/assassin/
  associatedPoints found the existing RelativeAssassin definition and consumer statements,
  but no relative-assassin base-change theorem.
- rg for the item id in WeilConjectures returned no matches.
- rg for relativeAssassin_baseChange_iff in WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json returned no matches.

No mathematical statement correction, new definition node, dependency replacement,
or STATEMENT-DISPUTED issue is needed.

Validation: the prescribed scompile.py wrapper compiled the sole delivered file both as
sandbox `Sheaf.Stage2.Sandbox0` and at its final library module name, in 3.0 and 3.1 seconds,
with no errors or warnings. Initial namespace/coercion elaboration failures were repaired
using `Limits.pullback`, explicit coercion to its point type, and `F.IsQuasicoherent`.
All universe variables are explicitly bound, and both automatic-implicit options are false.

## Second reading by Q82

Self-check only: this dispatched worker was explicitly instructed not to start other
agents; the maintainer performs the independent review. Reopened the node and final
module and checked every binder and clause as listed above. In particular the review
checked the tensor-factor order using pullback symmetry, that SpecOfPoint is the canonical
residual point, that coefficients use tensorPullback and remain quasi-coherent without
finite generation, and that association is tested fibrewise using the already recorded
annihilator/stalk definitions. The only dependency-list change adds the already landed
relative-assassin definition. No mathematical mismatch remained after the elaboration
repairs, and no independent reviewer is claimed here.
