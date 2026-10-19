## Worker report

Module `Sheaf.Paper.ConstantTwoTermResolution` states
`SheafOfModules.ConstantPrimePower.constant_two_term_resolution` with one postponed proof.
All other declarations are transparent abbreviations or constructions from existing data.
No definition is chosen from an unproved existence assertion. No source statement is corrected.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A small site is `{S : Type u} [SmallCategory S] (J : GrothendieckTopology S)`.
  This is the covering-sieve topology of the recorded site convention; no terminal object,
  points, nonempty objects, subcanonicity or global pullbacks are assumed.
  A site with initially different set universes can be represented in their maximum universe;
  there is no equality imposed between a geometric site's original universe parameters.
- The prime is `(l : ℕ) [Fact l.Prime]`; the exponent is `(n : ℕ) (hn : 1 ≤ n)`.
  `Coeff` is `ULift.{u} (PadicInt l)`, a universe lift with its existing ring structure.
  The lift permits every small site universe, including `u = 0`, without changing coefficients.
- `Modules J l` is the recorded `ringedSiteModules` of
  `constantCoefficientRing J (Coeff l)`. That ring is the underlying ring sheaf of
  `(constantSheaf J CommRingCat).obj (CommRingCat.of (Coeff l))`.
  It is the discrete constant ring sheaf, not an inverse limit of finite coefficient sheaves.
- `freeModule J l` is `constantCoefficientModule` applied to the ordinary rank-one module.
  It is the associated constant R-module; its canonical identification with the coefficient
  unit comes from sheafifying the identity action. This is the R in both terms of C.
- `reductionRingHom l n` is exactly `RingHom.ulift (PadicInt.toZModPow n)`.
  `quotientModule` restricts the ordinary module `ULift (ZMod (l ^ n))` along that map.
  `quotientSheaf J l n` applies the same recorded constant module sheafification functor.
  Thus Q has the specified underlying constant finite abelian sheaf and the canonical R-action.
  `reductionLinear` and `quotientMap` retain precisely this quotient homomorphism.
- The complex is presented up to its degreewise identifications:
  existential `K`, `em : K.X (-1) ≅ freeModule J l`, `e0 : K.X 0 ≅ freeModule J l`,
  vanishing `∀ i, i ≠ -1 → i ≠ 0 → IsZero (K.X i)`, and
  `K.d (-1) 0 = em.hom ≫ ((l ^ n) • 𝟙 _) ≫ e0.inv`.
  Natural-number scalar multiplication of the identity is multiplication by the integer l^n.
  This specifies exactly the two-term complex; other differentials vanish because their source
  or target is zero. The existential presentation uses isomorphic models of the fixed complex,
  not arbitrary differentials or an assumed resolution.
- Flat terms are `∀ i, IsFlatOnSite (R := ...) (K.X i)` with the coefficient sheaf explicit.
  K-flatness is the dependency's exact `CochainComplex.IsKFlatIndependentCoefficients K`.
- The quotient augmentation is `ε : K ⟶ single J l (quotientSheaf J l n)` with
  `ε.f 0 ≫ singleObjXSelf.hom = e0.hom ≫ quotientMap J l n` and `QuasiIso ε`.
  The target's other degrees are zero. Consequently the displayed equation fixes the map
  completely, including all degrees, and is precisely the quotient augmentation.
- For EVERY module sheaf L, without an injectivity assumption, `φ` is an isomorphism
  `(siteSheafTensorRight Q).obj L ≅ cokernel ((l ^ n) • 𝟙 L)`.
  This is the sheaf quotient L/l^n L, not a sectionwise quotient presumed to be a sheaf.
  Its normalization on each U, x and constant coefficient a says that the image of
  `siteSheafTensorTmul L Q U x (q (constantSection a))` is the cokernel class of
  `constantCoefficientUnit(a) • x`. This renders x tensor a-bar maps to a[x].
  `constantSection` is explicitly the module-sheafification adjunction unit; it is not
  a section of the ring sheaf wrongly used as a section of the rank-one module construction.
  All Q sections locally come from such constant coefficients, so the equation determines
  the sheaf map, including for sites with no points.
- The additional hypothesis on L is exactly `Mono ((l ^ n) • 𝟙 L)`.
  Kernels of module sheaves are computed sectionwise, so this means injectivity of
  multiplication by l^n, as stated by the node; no flatness on L is assumed.
- `total J l L K` is literally `CochainComplex.mapBifunctor (single L) K (curriedTensor _)`
  with the recorded canonical `SheafOfModules.monoidalCategory`, hence the signed total tensor.
  The augmentation `α` goes from this total to `(L tensor Q)[0]` and satisfies `QuasiIso α`.
  Its equation after `zeroSummand` is `id tensor (e0.hom ≫ q)`, using the single-complex
  degree-zero identification. `zeroSummand` is the canonical total-tensor summand inclusion,
  converted by the EXISTING `siteSheafTensorRightIso` from the explicit tensor to the monoidal
  tensor. The only nonzero total summand in degree zero is (0,0), so this equation determines
  the augmentation completely. It is exactly the tensor of the quotient augmentation,
  followed by the canonical concentration-in-degree-zero comparison. No arbitrary map or
  arbitrary comparison is used.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`, `CategoryTheory.Precoverage.IsSiteForCoverings`:
  the site's covering convention; the statement uses its associated Grothendieck topology.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf`:
  sheafification of the constant presheaf.
- `Mathlib.NumberTheory.Padics.PadicNumbers`, `Padic`; `PadicIntegers`, `PadicInt`;
  `RingHoms`, `PadicInt.toZModPow`: the recorded l-adic coefficient Mathlib match,
  ordinary quotient map and quotient module. The actual signature and source were read.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  the existing `SheafOfModules` category, not a second category.
- `Mathlib.Algebra.Homology.HomologicalComplex`, `CochainComplex`;
  `Mathlib.Algebra.Homology.QuasiIso`, `QuasiIso`;
  `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`:
  cochain complexes, quasi-isomorphisms, and the signed total tensor.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, `SheafOfModules.IsFlatOnSite`:
  exactness of the explicit sheaf tensor functor.
- `Sheaf.Algebra.Homology.KFlat`,
  `CochainComplex.IsKFlatIndependentCoefficients`: acyclic-tensor definition of K-flatness.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`,
  `SheafOfModules.siteSheafTensorSecondMap`, `siteSheafTensorTmul`, with the publicly
  retained `TensorProductOfUniverses.siteSheafTensorRight`: existing sheaf tensor and maps.
- Added existing statement dependency `def-weil-pbc-constant-coefficient-scalar-extension`,
  `Sheaf.CategoryTheory.ConstantCoefficientScalarExtension`: recorded `constantCoefficientRing`,
  `constantCoefficientUnit`, `constantCoefficientModule`, together with the publicly imported
  `strictPerfectConstantPresheaf` and Mathlib's `PresheafOfModules.sheafificationAdjunction`.
  This existing interface supplies the exact associated constant modules and their sections;
  no new notion, new node, or dependency repair is needed.

The module also imports the stated proof dependencies: `StandardQuotientsPerfect`,
`AlgebraicGeometry.standard_quotients_perfect`; `TensorClosed`,
`SheafOfModules.tensorClosed`; `BoundedAboveFlatSheafKFlat`,
`CochainComplex.isKFlat_of_boundedAbove_flat`; `TensorColimitsIndependentCoefficients`,
`SheafOfModules.tensorLeft_preservesColimits_independentCoefficients`.
The last module additionally supplies `siteSheafTensorRightIso`, used in `zeroSummand`.
Its current published source was read through `scompile.py --source` because the module
was absent in the older local checkout. Exact sheafification and the cohomology formulas
use the recorded Mathlib declarations in `Sites.Sheafification` and
`Algebra.Homology.ShortComplex.HomologicalComplex`. The docstring contains all five
DAG proof steps, with their dependency IDs and the canonical map calculations.

Edge cases checked mathematically before writing:

- The empty site and the topology admitting empty covers require no extra hypothesis;
  the relevant module category may be zero, and all conclusions still hold.
- On the point site, l = 2 and n = 1 gives the familiar resolution
  `[Z_2 --2--> Z_2] → (Z/2)[0]` with the ordinary reduction map.
- L = 0 is allowed and satisfies the injectivity condition; both tensor complexes are zero.
- L = R satisfies injectivity; L = the constant Q_l module has zero quotient and an
  acyclic tensor complex, as required.
- L = Q gives a valid quotient identification but multiplication by l^n is zero,
  so its negative cohomology is nonzero on a point site. This confirms why only the
  augmentation clause has the injectivity condition, and why it cannot be omitted.
- n = 0 is excluded precisely by the node's `hn`; l = 0 or 1 is excluded precisely
  by primality. Universes are explicit and no auto-bound implicits are enabled.

Searches made for an existing statement (before writing):

- `msearch.py` LeanFinder: "On a small ringed site the constant Z_l sheaf two term complex
  with differential l^N is a K flat resolution of Z/l^N and tensor resolves torsion free
  sheaves". Eight generic hits, including `Sheaf.H`, `Module.Flat.lTensor_shortComplex_exact`,
  and `SheafOfModules.instAbelian`; none states this constant resolution with its augmentations.
- `msearch.py` Loogle: `PadicInt.toZModPow, QuasiIso`; zero hits.
- `msearch.py` grep: `constant.*[Rr]ing|twoTerm|two_term` under `Algebra/Category/ModuleCat`;
  zero hits for the full resolution interface.
- `msearch.py` LeanSearch: "A two term complex of constant l adic integer sheaves resolves
  the constant prime power quotient and tensoring with a torsion free sheaf resolves its
  quotient". Eight generic constant-sheaf hits, including `constantSheaf` and
  `Sheaf.isConstant_iff_mem_essImage`; no matching theorem.
- `rg` in upstream `WeilConjectures` for the exact node ID: no match. Searches there and
  in `lean/Sheaf` for `constant_two_term_resolution|ConstantPrimePower|constant.*two.term|
  two.term.*constant`: no existing matching declaration. A broad search for constant modules
  and two-term constructions found the recorded constant-module functors, coefficient scalar
  extension, tensor infrastructure and ordinary coefficient resolution. Those declarations
  were read and reused. Mathlib constant module/sheaf directories supplied generic
  sheafification and constant-sheaf APIs, not the whole node.

Validation: the complete module passed `scompile.py` local file-only compilation and the
wrapper's server library confirmation. The only postponed theorem is
`constant_two_term_resolution`, whose entire proof is `sorry`. Temporary `#check` diagnostics
were removed before delivery. Definitions contain actual functorial constructions and
existing map laws. There is no `STATEMENT-DISPUTED` issue.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
