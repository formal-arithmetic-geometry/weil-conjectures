## Worker report

Repair of immutable head db27474ec5b9 for `lem-pur-etale-closed-constant-tensor`.
The saved packet first passed the prescribed dry run (ce014cf953), but the required
mathematical self-check found that R1-R4 were still present; they are repaired below.
The natural-language statement is unchanged. The item additionally cites the already
landed `lem-kun-tensor-sym`, whose canonical derived symmetry is used.

The module is `Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor`, with main theorem
`AlgebraicGeometry.Etale.closedConstantTensor` and a named flatness lemma
`AlgebraicGeometry.Etale.closedConstantModule_flat`. Both proofs are `sorry` at stage 2.
Definitions contain actual data, never an existence choice or arbitrary morphism.

Hypotheses and clauses:

- `(A : Type (u + 1)) [CommRing A]` supplies any commutative coefficient ring,
  using the project's coefficient-size convention; `X : Scheme.{u}` is arbitrary.
- `i`, `j`, `k` and their `IsClosedImmersion` instances supply the three closed
  supports C, D, E. `v : X' ⟶ X` is an arbitrary scheme morphism.
- `constantModuleSheaf A C` is the constant module A_C; `closedConstantModule A i`
  is its ordinary `lowerStar` direct image. `intersectionSupport i j` is C×_X D→X.
- `closedConstantPullbackMap` uses the published constant-section transition and
  `lowerStarComp`. `closedConstantPullbackAdjoint` is its adjunction mate, the
  specified b_{v,C}. The first three `IsIso` conjuncts assert invertibility for C,
  D and their intersection. No arbitrary isomorphism replaces this map.
- The three `closedConstantPullbackRestriction` clauses identify the specified b
  with restriction of constant sections via `upperStarConstantSheafIso`.
- `closedConstantPullbackCoherence A i`, `A j`, and `A (intersectionSupport i j)`
  state identity and composition, using `upperStarId`, `upperStarComp` and the
  named identity/composition support-change maps.
- `closedConstantRestriction` and `closedConstantRestriction₂` are restriction
  to the intersection. `constantModuleMultiplication` is multiplication of the
  constant tensor unit. `closedConstantTensorMap` tensors these restrictions and
  applies the lax-monoidal direct image and pointwise multiplication. Its `IsIso`
  clause asserts exactly μ_{C,D} is invertible.
- The three `ObjectProperty.flat` clauses say tensoring with P_C, P_D and P_I is
  exact in the fixed-coefficient sheaf category. The named flatness theorem states
  this for every closed support and supplies the proof witness used by the derived
  computation. Its proof docstring gives the identity-or-zero geometric-stalk argument.
- `closedConstantTensorCoherence A i j k` states ordinary associativity and symmetry.
  Associativity composes the left parenthesized product with
  `closedConstantAssociativitySupportMap`; symmetry composes with
  `closedConstantSymmetrySupportMap`. These are equalities of parallel morphisms.
- `closedConstantTensorPullbackSquare A i j v` uses the published oplax tensor
  comparison and composes b_{v,I} with `closedConstantBaseChangeSupportMap`.
- `closedConstantDerivedTensorMap` has actual `derivedTensor` source. It is
  `singleFunctorObjTensorIso ... (closedConstantModule_flat A i)` followed by the
  single functor's image of the same ordinary μ. Its invertibility is asserted in
  the main theorem's `IsIso (closedConstantDerivedTensorMap A i j)` conjunct.
- `ClosedConstantDerivedTensorCoherence A i j k` has fields `associativity` and
  `symmetry`, stating derived associativity and symmetry using derived tensor morphisms, associator and braiding, and the single
  functor's images of the same support identifications. Its
  `associativity.w` is the associativity equality; `symmetry` is the symmetry equality
  directly. They use the actual `derivedTensor.map` operations,
  `derivedTensorAssociator`, and the canonical `derivedTensorSymmetry`.
- `closedConstantDerivedPullbackMap` is the image of b after
  `singleFunctorCompLeftDerivedUpperStarIso`. The derived pullback square uses
  `leftDerivedUpperStarTensorComparison` and these same b and μᴸ maps, with the
  image of the base-change support map. Its `commutes.w` is precisely the displayed
  derived equality. It is the `commutes` field of
  `ClosedConstantDerivedTensorPullbackSquare A i j v`, the main theorem's last conjunct.

Return repairs:

R1: Removed every `HEq`. `closedConstantSupportChange` is the existing
`constantModulePushforwardMap`. The five named specializations use universal
`pullback.lift` maps and `pullbackSymmetry`, in the contravariant direction on
constant-section direct images. These compare different chosen fiber products
canonically, without asserting equality of their objects.

R2: Replaced the single-functor-only derived map with the canonical K-flat
computation `singleFunctorObjTensorIso`; added actual derived associativity,
symmetry and pullback square as the proof fields of two proposition structures.
Their fields display the actual derived equations; no data or arbitrary maps are added.
The derived formulas use the actual derived bifunctor's maps and
`derivedTensorAssociator`, rather than asking the kernel to compare that bifunctor with
a newly inferred monoidal tensor. The upstream TensorStructure implementation notes
identify precisely this costly comparison. `closedConstantDerivedPairMap` maps two
arrows with the same bifunctor; it is exactly the usual tensor of those arrows. Every derived product is the existing derived
monoidal tensor, whose bifunctor is `Etale.derivedTensor`. The helper `closedConstantFlatModelMap` composes the flat computation and the
single functor map with abstract coefficients; the supported multiplication
specializes this actual composite to ModuleCat A. The multiplication
has an explicit source P_C[0]⊗ᴸP_D[0] (using `derivedTensor`) and target P_I[0].
The derived b also has an explicit degree-zero signature. Associator and comparison
endpoints are inferred from these typed arrows, keeping the published instances throughout. The small upstream
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB` module supplies its published
`ModuleCat.isGrothendieckAbelian_of_commRing` shortcut. Its documentation identifies
the exact kernel timeout caused by abstraction of the generic ring-instance proof;
reusing this instance avoids that reduction without changing any mathematical data.

R3: Took the explicitly authorized option to drop the `IsFlatOnSite` clauses
and removed `constantRingedModel` and the constant-ring equivalence import.
Flatness remains exact tensoring in the already accepted fixed-scalar category.
No `.choose` of a mere existence equivalence remains.

R4: The report now gives the full arguments `A i j k` (and `v` for the final derived
clauses), has one second-reading heading, and `lean.note` explains why the
fixed-scalar global sheaf tensor (the published wrapper of `Sheaf.monoidalCategory`)
is the specialization of the site's
sheafified balanced tensor. Locally every section of the constant ring sheaf
comes from A. Thus sheafification imposes exactly the same balancing relations;
exactness is the same notion in the fixed-coefficient encoding. This follows the
node's proof step 5 and retains the tensor interface accepted by the returned review.

Dependency declarations used:

- `WeilConjectures.AlgebraicGeometry.ConstantModulePushforwardFunctoriality`:
  `AlgebraicGeometry.Etale.constantModulePushforwardMap`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` and `.Monoidal`:
  `lowerStar`, `upperStarLowerStarAdjunction`, `lowerStarComp`, `upperStarId`,
  `upperStarComp`, `Scheme.upperStarConstantSheafIso`, and the canonical lax/oplax structures.
  `.FlatModuleCat` supplies `upperStarPreservesFlat_moduleCat` for arbitrary A.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`:
  `ModuleCat.isGrothendieckAbelian_of_commRing`, the existing atomic instance shortcut.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`:
  `AlgebraicGeometry.Etale.derivedTensor`.
- `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`:
  `AlgebraicGeometry.Etale.derivedTensorAssociator`, with its explicit derivedTensor endpoints.
- `WeilConjectures.SixFunctors.Etale.Derived.Invertible`:
  `AlgebraicGeometry.Etale.singleFunctorObjTensorIso`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar` and
  `.UpperStarMonoidal.Comparison`: `singleFunctorCompLeftDerivedUpperStarIso`
  and `leftDerivedUpperStarTensorComparison`.
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`:
  `AlgebraicGeometry.Etale.derivedTensorSymmetry`, the landed `lem-kun-tensor-sym`
  interface for the actual signed symmetry (no arbitrary choice of braiding).
- Mathlib: `constantSheaf`, `pullback`, `pullback.lift`, `pullbackSymmetry`,
  `IsClosedImmersion`, `ObjectProperty.flat`, `DerivedCategory.singleFunctor`,
  the sheaf monoidal tensor, associator, braiding, and `tensorHom`.

Edge cases rechecked: empty scheme, empty supports, zero coefficient ring,
identity v, two successive arbitrary morphisms, nonreduced supports, and
interchanged/parenthesized intersections. The support maps exist in all these
cases by universal properties; no finite-type, separatedness, reducedness,
Cartier or etaleness hypothesis on v has been added. No statement dispute remains.

Search evidence retained from the original packet: LeanFinder query "closed immersion
constant sheaves on small etale sites are flat and tensor to the constant sheaf on
the intersection naturally under arbitrary pullback" found only unrelated general
sheaf/flatness results. LeanSearch query "closed support direct image constant sheaf
tensor intersection base change flat etale" found only general sheaf/flatness results.
Loogle `CategoryTheory.Sheaf.tensorProd_isSheaf` found the existing sheaf tensor,
not this closed-support theorem. Mathlib grep `closed.*(tensor|flat)|support.*cup|cup.*support`
and project grep `closed.*(constant|tensor)|constant.*closed` found no exact theorem.
For this repair, `rg` found the published `singleFunctorObjTensorIso` in Etale's
Derived.Invertible, and the derived pullback comparison and degree-zero compatibility
in Derived.UpperStarMonoidal.Comparison and Derived.UpperLowerStar. Their full
signatures and docstrings were read. A comparison of the inferred concrete coefficient
instances found the documented commutative-ring shortcut in
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`; that existing module is imported. A further `rg` search for associators found the existing `derivedTensorAssociator`
in Derived.TensorStructure; its full signature, docstring and implementation notes
were read and its exact bifunctor interface is reused. The live source of the constant-module
transition was retrieved with `scompile.py --source` and reused unchanged.

## Second reading by N3

The dispatcher forbids additional agents; this is the worker's explicit self-check,
followed by the maintainer's independent immutable-head review. Read the node and
module side by side. The repairs preserve the accepted b, μ, restriction and flatness
clauses. Each former heterogeneous equation now has one common codomain after its
named support map. The derived source is genuinely P_C[0]⊗ᴸP_D[0], with its K-flat
computation; the derived equations use derived maps and the canonical derived tensor
comparison. No chosen constant-ring model remains. The node's statement text is unchanged; its statement dependencies gain only the
already landed canonical symmetry node.

Validation: the final module passed `scompile.py N3 lem-pur-etale-closed-constant-tensor`
with exit code 0, both as the sandbox file (23.9 s) and at the library module path
(16.0 s). There are no errors or non-sorry warnings and no debug or heartbeat settings
in the delivered file. The node signature was re-extracted verbatim from that file.
Against the shared current node, only `lean` and the added landed symmetry dependency
in `stmt_deps` differ; the natural-language statement and proof are unchanged.
