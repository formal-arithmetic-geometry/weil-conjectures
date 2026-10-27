## Worker report

The module `Sheaf.CategoryTheory.HomogeneousPolynomialAugmentedResolution` states the
node without changing its mathematical statement. The only postponed theorem is
`Profinite.CondensedAction.HomogeneousPolynomial.homogeneous_polynomial_augmented_resolution`.
All other declarations are explicit finite polynomial definitions or specifications of
uniquely identified data. The theorem has the full eight-step natural-language proof.
No definition chooses an object from a bare existence assertion.

Clause-by-clause correspondence:

- Prime ell: `(ell : ℕ) [Fact ell.Prime]`.
- Algebraic closure with its extended norm topology: `(Ω : Type u) [NormedField Ω]
  [NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]`. The extension norm is unique;
  no `CompleteSpace Ω` is assumed. The finite intermediate field is
  `(E : IntermediateField ℚ_[ell] Ω) [FiniteDimensional ℚ_[ell] E]`.
- Both choices of coefficients: `Assertion ell E r ∧ Assertion ell Ω r`.
  `continuousScalarRing F` bundles the recorded all-continuous condensed ring,
  with sections `ULift C(S,F)`. There is no finite-subextension restriction or completion.
- Rank r is an arbitrary natural number. The acting group is exactly the recorded
  `Profinite.LadicLattice.Lattice.{u} ell r`, the multiplicative tag on the universe
  lift of `Fin r → ℤ_[ell]`, with its original product topology and additive group law.
- Internal modules/actions: `CondensedBar.Equivariant (continuousScalarRing F) L`,
  which abbreviates the recorded `CondensedAction.ActionModule`. Its action fields
  are section-ring-linear monoid homomorphisms natural in every profinite test object.
- Size convention: `Profinite.{u}`, coefficients `F : Type u`, section groups
  in `Type (u+1)`, and `DerivedCategory.Q.{u+1}`. The site and every parameter type
  occur within this coefficient bound. Universe polymorphism permits enlarging u.
- K^n is the direct sum on monomials in (n+1)r variables: `Model.ι n` is indexed by
  `(Fin (n+1) × Fin r) →₀ ℕ`; `Model.isColimit n` is the coproduct universal property
  for these copies of `Mod.regular A.X` in the actual internal-module category.
  `Model.negative` makes every negative integer degree a zero object.
- Diagonal translation: `translatedMonomial` uses `MvPolynomial.eval₂Hom`, sending
  each X_(a,i) to X_(a,i) minus the continuous function
  `s ↦ algebraMap ℚ_[ell] F ((g s).toAdd.down i : ℚ_[ell])`.
  `Model.translation` imposes that formula on every monomial with every coefficient,
  for every S and every g in C(S,L). The finite-support sum fixes the action entirely.
- Individual substitutions are internal A-linear: `Model.face n i` is an equivariant
  morphism; `Model.face_formula` specifies coordinate omission by `i.succAbove`.
  `Contraction.h` and `Contraction.h0` are internal-module morphisms, and their
  formula fields specify positive-degree zero insertion and degree-zero evaluation.
- Differential: `deletion` is the finite sum of these renamings with sign
  `(-1 : ℤ)^i.val`. `Model.differential` pins its value on every monomial generator,
  hence on the full coproduct by A-linearity. `Model.cochain` includes delta squared
  zero and equivariance of the differentials.
- Constant augmentation: `Model.augmentation` is a cochain map from the degree-zero
  single complex of the regular module with the recorded trivial action.
  `Model.augmentation_zero` uses the canonical `singleObjXSelf` identification to
  equate it with the zero-exponent monomial injection. Outside degree zero the
  single complex is zero, so its other components are necessarily zero.
- h in positive degrees: `insertZero` substitutes zero in block zero and X_(j,i)
  in block j+1; `Contraction.h_formula` imposes it on every monomial.
  `Contraction.h0_formula` makes evaluation at zero identity on the constant
  monomial and zero on every nonconstant monomial.
- h^0 a = 1: `Contraction.split`. The degree-zero identity is
  `Contraction.zero_identity`; arrows compose in diagrammatic order.
  `Contraction.positive_identity n` states delta^n h^(n+1) + h^(n+2) delta^(n+1)
  on degree n+1, which covers precisely every strictly positive degree.
- Parameter restriction: all face, augmentation, h and h0 maps are actual internal
  morphisms, so their underlying natural transformations commute with every map
  of profinite parameters. No equivariance of h or h0 is required by their types.
- Existence: `Assertion` includes `Nonempty (Model ell F r)`, and for every such
  model includes `Nonempty (Contraction ell F r P)`. These are properties of pinned
  coproduct data; no `Classical.choice` definition is made from their existence.
- Quasi-isomorphism in the equivariant abelian category: `QuasiIso P.augmentation`.
  The canonical abelian structure comes from the recorded restriction-calculus
  imports, whose `forgetExact` creates kernels/cokernels and detects exactness.
- Ordinary derived category: `IsIso (DerivedCategory.Q.{u+1}.map P.augmentation)`
  for the actual augmentation, rather than an arbitrary derived arrow.
- Rank zero remains included: the exponent type has exactly the zero vector;
  omission/insertion maps are identity, and the signed differential alternates
  zero (even n) and identity (odd n). Nothing assumes r positive.

Dependency declarations read and used:

- `Sheaf.Topology.ContinuousMapCondensedRing`: `Profinite.continuousMapRingObjOfUniverse`,
  `continuousMapRingObjOfUniverseMonObj`, and the corresponding sheaf construction,
  as bundled by `Sheaf.CategoryTheory.ContinuousScalarRing` /
  `Profinite.CondensedAction.continuousScalarRing`.
- `Sheaf.Topology.LadicLattice`: `Profinite.LadicLattice.Lattice`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, `Mod.regular`.
- `Sheaf.CategoryTheory.CondensedActionModule`: `Profinite.CondensedAction.ActionModule`,
  `trivial`, the action category and its sectionwise additive structure.
- `Sheaf.CategoryTheory.CondensedEquivariantBarData`: `CondensedBar.Ring`, `Modules`,
  `Equivariant`, all abbreviating the recorded underlying definitions.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionModuleFunctor` / `sectionModuleEquivalence`,
  used by the action interface and its unchanged section maps.
- `Mathlib.Algebra.MvPolynomial.Basic` / `.Eval`: `MvPolynomial`, `monomial`,
  `rename`, `eval₂Hom`, and finite-support coefficient expansion; read `aeval` and
  `algHom_ext` for the recorded universal property as well.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and quasi-isomorphisms.
- `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`: its imported
  `CondensedDerivedRestriction.actionAbelian` and `forgetExact` supply the
  equivariant abelian interface; its full recorded signatures and proof were read.
- Proof-only imports: `Mathlib.CategoryTheory.Sites.Coherent.SheafComparison`
  (`Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition`) and
  `Sheaf.CategoryTheory.SheafTensor` (`sfbSheafTensor_properties`). The internal
  module equivalence and action definitions are already public statement dependencies.
- `def-weil-size-convention` is metatheoretic, rendered by the explicit universe u.

The three added stmt_deps are already-landed definition nodes:
`def-sfb-bundled-continuous-scalar-ring`, `def-sfb-condensed-equivariant-bar-data`,
and `def-weil-pbc-internal-abelian-sheaf-module-equivalence`. They own existing
interfaces used above. No new node or dependency repair is required.

Edge checks: r=0; n=0 and n=1 (delta^0 f(y0,y1)=f(y1)-f(y0), so insertion
of zero gives f-f(0)); empty profinite S (zero section ring/module); zero
coefficient sections; arbitrary finite polynomial degree; every negative integer
degree; the uncompleted algebraic closure; both scalar fields. No extra finiteness,
completeness, nonemptiness, positive-rank, or equivariance-of-h assumption is used.

Searches (2026-10-24):

- msearch LeanFinder, "Homogeneous polynomial augmented cochain complex with diagonal
  translation and insertion of zero contracting homotopy": 8 hits including
  `CochainComplex.mkHomAux`, `.augment`, and `Homotopy.mkCoinductive`, no polynomial
  equivariant resolution with the specified internal section action.
- msearch Loogle, "MvPolynomial, Homotopy": 0 hits.
- msearch grep, `polynomial.*(contract|resolution)|(contract|resolution).*polynomial`:
  11 hits, about separable contraction and polynomial expansion, no resolution match.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for homogeneous polynomial / polynomial
  resolution: existing homogeneous polynomials, cotangent resolutions and
  `PolynomialDerivedBarComparison`. The latter is the downstream derived-invariants
  comparison, not this equivariant augmented resolution. Its `PolynomialBar.Complex`
  has nr variables and the inhomogeneous differential, so it cannot replace this node.
- Exact node-id search in `lean/WeilConjectures`: no declaration.
- Read current blueprint `latest/.../sk-thm-sf-ctf-stability-direct-images.proof.md`:
  paragraph (3) delegates the open-direct-image input as the node's source records.

No statement correction or STATEMENT-DISPUTED flag is needed. The explicit formulas
are consistent in all checked cases. Compiler validation and delivery preflight are
run with the prescribed wrappers only.

## Second reading by Q116

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
