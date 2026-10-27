## Worker report

This delivery states `AlgebraicGeometry.ProEtale.adicAffineFinitenessDescent` in
`Sheaf.AlgebraicGeometry.AdicAffineFinitenessDescent`. The sole proof is `sorry`.
There are no definitions, new nodes, dependency repairs or statement changes.
The theorem has the reviewed node's eight-step proof in its docstring.

The previous worker's stale-assignment diagnosis confused the reviewed stage-1
split with completion of stage 2. The current node has `reviewed` by NU but no
`lean` or `reviewed_lean`. NU's own report is explicitly a stage-1 delivery and
states that no declaration of this conditional theorem exists. This delivery
retains NU's reviewed statement and proof, adding only its Lean record.

### Statement correspondence

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Fixed algebraic closure Omega of Q_ell, with the extending absolute-value
  topology: the existing `PadicAlgCl l = AlgebraicClosure (Padic l)` chosen by the
  native framework. Mathlib's `NumberTheory.Padics.Complex` gives its spectral
  `NormedField`, `NormedAlgebra` and `PadicAlgCl.norm_extends`. On a finite
  subextension this is the unique extending absolute value, as in the recorded
  coefficient-extension dependency. Choosing this fixed algebraic closure is
  the node's choice of Omega, with no completeness assumption on Omega. Omega
  is not replaced by the completed field `PadicComplex l`.
- Algebraically closed base field of characteristic different from ell:
  `(K : Type u) [Field K] [IsAlgClosed K] (_hK : ringChar K ≠ l)`.
- B_V consists of continuous functions on the WHOLE underlying space of a
  pro-etale test scheme whose values locally span a finite-dimensional Q_ell
  subspace: `PadicAlgCl.locallyFiniteFunctions` and
  `ProEtale.adicConstantSheaf`, with `adicConstantSheaf_obj_obj` giving exactly
  these sections. The site is Mathlib's recorded `Scheme.ProEt`, with
  `Scheme.ProEt.topology`.
- A(V) is modules over B_V: the existing `ProEtale.AdicSheaf l V`, namely internal
  modules over this Omega-algebra sheaf in sheaves of Omega-vector spaces.
  This is the native presentation of ordinary B_V-module sheaves: restriction
  along constant functions gives the Omega-action on an ordinary module, and
  the internal action is its sectionwise B_V-action. Conversely that action
  gives the ordinary module. Objects and linear sheaf maps are the same data;
  no arbitrary equivalence or extra structure is assumed.
- Pro-etale locally finite free, with rank allowed to vary by covering member:
  `IsAdicLisseSheaf` has `∀ f, R f → ∃ n : ℕ, Nonempty (...)`.
  Finite locally closed constructible strata: `IsAdicStratifiedLisseSheaf`
  quantifies over a finite index type, immersions, constructible images and a
  unique stratum through every point. `IsAdicConstructibleSheaf` makes this
  Zariski local. In particular the actual definition includes constructible
  images, despite an older explanatory paragraph discussing locally closed
  strata. `IsImmersion` gives the locally closed subscheme condition.
- Ordinary derived category: `DerivedCategory (AdicSheaf l V)`, with the native
  Grothendieck/K-injective derived-category instance. There are no fixed pairs,
  Weil actions, completed coefficients or alternative derived categories.
- D^b_c: `DerivedCategory.TStructure.t.bounded` is existence of finite lower and
  upper integer bounds. `DerivedCategory.homologyProperty
  (adicConstructibleSheaf l V)` means constructible H^n for EVERY integer n.
- Ordinary g_* with action by precomposition: `adicLowerStar l g` is the
  existing module direct image along `adicConstantSheafToLowerStar l g`.
  The latter is explicitly `locallyFiniteFunctionsComp` along the pullback
  projection. Its `rightDerivedFunctor` is the ACTUAL total derived functor
  on the unbounded ordinary derived categories.
- Affine hypothesis: `h_affine` quantifies over every `A B : Scheme.{u}` with
  `[IsAffine A] [IsAffine B]`, every `t : B ⟶ Spec (CommRingCat.of K)` with
  `[LocallyOfFiniteType t]`, every `g : A ⟶ B` with
  `[LocallyOfFiniteType g]`, and every `M : AdicSheaf l A` satisfying
  `IsAdicConstructibleSheaf M`. The two conclusions are boundedness and
  constructibility of all cohomology of `Rg_*(M[0])`; degree zero is
  `(DerivedCategory.singleFunctor _ 0).obj M`. The same `l` and `K` occur
  throughout. No geometric hypotheses on g beyond those in the node occur.
- Target is a K-scheme locally of finite type and quasi-compact:
  `(s : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType s]
  [CompactSpace Y]`. Here `CompactSpace` means quasi-compact with no Hausdorff
  requirement. The source gets its K-structure by `f ≫ s`.
- Morphism is qcqs and locally finite type:
  `(f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]`.
  Neither separatedness nor absolute quasi-separatedness is added as a binder.
- Every bounded constructible complex:
  `(L : DerivedCategory (AdicSheaf l X)) (hL : ...bounded L)
  (hLc : ...homologyProperty ... L)`. The conclusion is the same conjunction
  for `(adicLowerStar l f).rightDerivedFunctor.obj L` on Y. The bounds may
  depend on L; no uniform cohomological dimension is asserted.

### Dependency declarations read and reused

All ten statement-dependency nodes, their records, and source declarations were
read. The geometric definitions are `AlgebraicGeometry.LocallyOfFiniteType`
(`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`), `QuasiCompact`
(`...Morphisms.QuasiCompact`) and `QuasiSeparated`
(`...Morphisms.QuasiSeparated`). The site is `AlgebraicGeometry.Scheme.ProEt`
(`Mathlib.AlgebraicGeometry.Sites.Proetale`). The strata use the recorded
`IsLocallyClosed` (`Mathlib.Topology.Defs.Basic`) through `IsImmersion`, and
`Topology.IsConstructible` (`Mathlib.Topology.Constructible`) directly in the
existing stratification predicate. `AlgebraicClosure` / `IsAlgClosure`
(`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` / `.Basic`) underlie
Mathlib's `PadicAlgCl`. The coefficient-extension record
`Padic.finite_coefficientExtensionRing` and the constructions it imports from
`Sheaf.NumberTheory.Padics.CoefficientExtension` were read; their spectral
absolute-value convention agrees with the existing coefficient sheaf. Their
module is imported, without imposing a finite extension coefficient field.

`CategoryTheory.ringedSiteModules` in
`Sheaf.CategoryTheory.RingedSiteModules` is the ordinary sheaf-module presentation;
its module is imported. We reuse the already existing native `AdicSheaf`,
`adicLowerStar`, `IsAdicLisseSheaf`, `IsAdicStratifiedLisseSheaf`,
`IsAdicConstructibleSheaf`, and `adicConstructibleSheaf` from
`WeilConjectures.SixFunctors.ProEtale.Adic.Module` / `.Constructible`.
No new copy of any category, coefficient ring or predicate is introduced.

`DerivedCategory` is the recorded Mathlib declaration in
`Mathlib.Algebra.Homology.DerivedCategory.Basic`. The recorded general
`CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` and its
unit/uniqueness interface in
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` were read and
imported. In this Grothendieck specialization the existing native
`CategoryTheory.Functor.rightDerivedFunctor`
(`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`)
already applies: the canonical K-injective-resolution instance is available,
so no resolution hypothesis is added. Its definition is `totalRightDerived` of
`F.mapHomotopyCategory ... ⋙ DerivedCategory.Qh` along `DerivedCategory.Qh`,
and its unit has `IsRightDerivedFunctor`. It is exactly the universal pair of
the dependency, uniquely isomorphic with its chosen generalized construction.
This uses an existing specialization of the dependency's notion, not a new
construction or an unusable dependency requiring a repair. It also matches the
native consumers' actual functor.

All proof dependencies with a recorded Lean module are imported as proof
imports. Unstated proof prerequisites stay as the reviewed DAG's proof tasks;
no extra assumption or postponed theorem is needed to type this statement.

### Edge cases and sizes

Checked before writing: the zero sheaf (finite free rank 0), the zero complex,
empty source, empty target, empty affine covers, repeated covering members,
negative as well as positive cohomological degrees, arbitrary characteristic
prime to ell including zero, and non-separated qcqs sources. Constructibility
on an empty scheme is vacuous. The native predicates include rank 0 and empty
stratifications; boundedness includes zero. No point, stratum or cover is
assumed nonempty. The overlap argument uses affineness only inside a fixed
affine open and uses quasi-separatedness for compactness of other overlaps.

The single explicit universe `u` contains K and the schemes; no independent
smaller test universe is used. `AdicSheaf l V : Type (u+2)` uses coefficients
lifted to the sheaf universe `u+1`, and the native Grothendieck instance gives
`HasDerivedCategory.{u+1}`. All variables are explicit, and
`set_option autoImplicit false` is in the file. No new instance, local notation,
private definition or hidden let-binding is used.

### Searches

Executed the prescribed msearch wrapper with:

- leanfinder, `conditional descent of bounded constructible derived direct image of adic sheaves from affine schemes to quasi compact quasi separated finite type morphisms`:
  eight scheme-limit and affine-descent hits; no adic conditional theorem.
- loogle, `AlgebraicGeometry.ProEtale.finiteLowerStar_of_bounded, AlgebraicGeometry.ProEtale.finiteFor_of_isAffine`:
  zero hits, unknown first upstream identifier; this did not establish a match.
- grep in Mathlib/AlgebraicGeometry,
  `AdicSheaf|IsAdicConstructibleSheaf|finiteLowerStar`:
  five hits in `Sites/ElladicCohomology.lean`, concerning the continuous
  Z_ell coefficient sheaf, not native rational adic affine descent.
- leansearch, `right derived direct image of constructible adic sheaves bounded constructible affine quasi compact quasi separated`:
  eight hits about generic derived functors and sheaf pushforwards, including
  `Functor.totalRightDerived`; none states the conditional descent.

Direct rg searches of `lean/WeilConjectures`, `lean/Sheaf`, and the relevant
DAG chapters used `nativeAdic|NativeAdic|adic-affine-finiteness-descent`,
`finiteFor_of_isAffine`, `AdicSheaf|IsAdicConstructibleSheaf|finiteLowerStar`,
and the locally finite continuous-function names. Exact item-id search of
`lean/WeilConjectures` had no match. Read `LowerStar.lean`'s full devissage
and target-localization declarations: `finiteLowerStar_of_bounded` and
`FiniteFor.of_quasiSeparatedSpace` provide pieces of this argument; the
unconditional geometric finiteness results invoke the affine theorem directly
and do not have this node's quantified affine hypothesis. Therefore none is
an exact existing declaration of this conditional statement.

### Validation

Compiled the delivered file with scompile.py against the live published build:
both sandbox and library-name checks passed cleanly (17.4 s and 13.8 s).
The initial probe mistakenly named a nonexistent Mathlib SingleFunctor module;
replacing that import with the existing SingleTriangle module fixed it.
No mathematical statement fault or STATEMENT-DISPUTED remains.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
