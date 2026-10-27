## Worker report

The module Sheaf.WeilSheaf.DerivedHomSingleResolution states the native
single-source derived internal-Hom comparison. Nothing is proved. The three
postponed theorems are singleResolutionProjection_comm,
singleResolutionProjection_isIso and derivedHom_single_resolution, all in
AlgebraicGeometry.ProEtaleWeilSheaf. Each is a clause or construction explicitly
specified by this node, has the node's blueprint tag, and has its natural-language
proof in its docstring. The two definitions have real data: the degree-zero
projection uses the first theorem for its chain-map proof, and the target map is
Qh of the actual product-Hom postcomposition map. No arbitrary comparison map or
choice from an undetermined existence assertion is introduced.

Hypotheses and objects, clause by clause:

- The finite field is `{k₀ : Type u} [Field k₀] [Finite k₀]`. The coefficient
  prime and the characteristic restriction are `{l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]`. The algebraic closure is the upstream
  `AlgebraicClosure k₀`; Qlb is `PadicAlgCl l`. These canonical models are the
  existing native models explicitly named by the node's source, and require no
  extra closure, embedding or field-of-definition hypothesis.
- X is `{X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]`. The main theorem
  explicitly binds `[LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]`.
  It does not assume separatedness, quasi-compactness or finite type.
- The geometric base change and inverse-q-Frobenius are the existing
  `Scheme.Hom.geometricFiber`, `geometricGaloisFrobenius`, and
  `WeilSheaf.frobeniusPullback`, as used by `ProEtaleWeilSheaf k₀ l X`.
- The pro-etale site is Mathlib's `Scheme.ProEt` with `Scheme.ProEt.topology`,
  the recorded dependency. Its object universe is u+1 and its arrow universe u.
  Coefficients use ULift to u+1; the category of sheaves/modules has object
  universe u+2. No equality between the site universes is imposed. These are the
  existing native universe choices implementing def-weil-size-convention;
  no extra smallness hypothesis or restricted class of site objects is added.
- R is precisely `adicConstantSheaf l` on the geometric fiber. I inspected
  `Adic/ConstantSheaf.lean`, `Adic/Ring.lean` and `Adic/Module.lean`:
  its sections are `ULift (PadicAlgCl.locallyFiniteFunctions l U.left)`;
  membership says locally finite-dimensional Q_l-span of the continuous image.
  `AdicSheaf` is the category of module objects over this sheaf, not merely
  sheaves of modules over the discrete constant field.
- The category A is `ProEtaleWeilSheaf k₀ l X`, definitionally
  `IsoAlgebra (WeilSheaf.frobeniusPullback k₀ l X)`. I inspected its underlying
  definition: `IsoAlgebra` is `(Algebra.IsIsoStr F).FullSubcategory`, where
  `IsIsoStr F A` is `IsIso A.str`. Thus this is exactly the specialization in
  def-weil-endofunctor-fixed-pair-category.mathlib_match; no second fixed-pair
  category is defined. Morphisms satisfy `F.map f ≫ B.str = A.str ≫ f`.
- The native D(A) is Mathlib `DerivedCategory (ProEtaleWeilSheaf k₀ l X)`;
  Q is `DerivedCategory.Q`. These are the recorded declaration and localization
  of def-weil-abstract-derived-category, not fixed pairs in an already-derived
  underlying category. The upstream Grothendieck instance supplies the existing
  derived category and K-injective resolutions without extra hypotheses.
- H and H_A are the existing `ihomBifunctor k₀ l X` and
  `ihomFunctor k₀ l X A`. I read `ihom_obj_str` in TateTwistCohomology.lean:
  its three factors are the pullback/Hom identification, precomposition by
  theta_A inverse, and postcomposition by theta_B. This is the node's conjugation.
- K-injectivity is `[I.IsKInjective]` (and `[J.IsKInjective]`), Mathlib's
  null-homotopy condition on maps from acyclic complexes. I read its definition.
  Alpha has only `[QuasiIso α]`, with no monomorphism, termwise injectivity,
  bounded complex, or lissity restriction.
- N has vanishing sufficiently negative cohomology: `∃ b : ℤ, N.IsGE b`.
  I checked `DerivedCategory.isGE_iff`: this is exactly
  `∀ i < b, IsZero ((homologyFunctor _ i).obj N)`. For a representative I the
  same condition is imposed on `DerivedCategory.Q.obj I`, so the complex itself
  may be unbounded. The bound is existential, not fixed to zero.
- The native bifunctor is `derivedHom k₀ l X N`, the exact existing definition
  singled out in the node. It is `bifunctorRHomOfComplex` on `kInjectiveRep N`,
  with the same K-injective first-variable model as the upstream definition.
  RH_A is the existing `ihomFunctor.rightDerivedFunctor`, computed by
  `rightDerivedFunctorObjQIso I`. This is the Fourier.lean model cited by the
  node, not an alternative derived operation.

Conclusion and canonical-map clauses:

- The existential family c gives, simultaneously for every A and every bounded-
  below K-injective representative I, an actual isomorphism in D(A) between
  `bifunctorRHomOfComplex H I (A[0])` and `RH_A(Q I)`.
- The first conjunct quantifies over EVERY K-injective J and EVERY resolution
  `α : A[0] ⟶ J`. Its equation identifies c followed by the standard termwise
  derived computation with: the native first-variable transport along inverse
  Q(alpha), `bifunctorRHomOfComplexObjIso`, Q of actual precomposition
  `bifunctorHomMapLeft α`, and Q of `singleResolutionProjection`.
  The first two factors are isomorphisms by construction and the last factor is
  a chain isomorphism by singleResolutionProjection_isIso. Thus the asserted
  equation also asserts invertibility of the specified localized precomposition,
  rather than just existence of an unrelated isomorphism. It covers any chosen
  resolution and gives the asserted source-choice independence.
- `singleResolutionProjection` is given degreewise by `bifunctorHomπ` at
  `(p,q) = (0,n)`, followed by the canonical single-complex degree-zero
  identification. Its companion commutation and invertibility theorems are the
  exact degree-zero chain identification in the node. Their docstrings describe
  the differential calculation and insertion of zero into every other factor.
- The second conjunct is the contravariant naturality square for every A -> B,
  using the native source functor and `rightDerivedFunctorNatTrans` of the
  existing ihomBifunctor source map.
- The third conjunct is the covariant naturality square for every chain map
  `g : I ⟶ I'` between arbitrary bounded-below K-injective representatives.
  `singleResolutionMapRight` is actual postcomposition on the same chosen
  source model used by bifunctorRHomOfComplex, followed by quotient and Qh.
  Every derived arrow between such targets has a chain representative unique
  up to homotopy (lem-weil-pbc-kinjective-hom-derived). The product-Hom
  construction respects these homotopies, so this is precisely naturality for
  all derived arrows, including the changes of target representative.
- The last conjunct gives the displayed native isomorphism for EVERY bounded-
  below N and every A, together with its normalization after transport along
  `kInjectiveRepIso N`. This normalization identifies it with the same c family.
  A cohomological lower bound transports along kInjectiveRepIso, so its universal
  hI clause is inhabited, not vacuous. The two preceding squares then give both
  naturalities of this comparison for arbitrary N. Their isomorphism cases and
  the first conjunct give independence of both chosen resolutions.
- No `IsLisse`, dual object, tensor product, constructibility predicate or
  `WeilSheaf` full subcategory occurs as a hypothesis on A.

Sign convention checked against the actual upstream declaration:
`bifunctorHomObj` uses the row-totalization differential with factor (-1)^p,
whereas the prose writes d_I f - (-1)^n f d_J. Their canonical chain
identification multiplies the degree-(p,n) factor by (-1)^(p*n):
`s(p,n+1)=(-1)^p s(p,n)` and `s(p+1,n)=(-1)^n s(p,n)` verify the differential.
This identification is natural in both complexes, commutes with the degree-zero
precomposition maps, and is identity on p=0. It therefore gives exactly the same
localized comparison and the same canonical single-source projection. The Lean
uses the node's explicitly cited native upstream definitions, with this usual
canonical identification of the two sign conventions. No statement change is
needed and no clause is dropped.

Dependency declarations inspected and used:

- Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.ProEt`, `ProEt.topology`.
- Mathlib.CategoryTheory.Endofunctor.Algebra: `Endofunctor.Algebra`,
  `Algebra.Hom`; upstream
  WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra:
  `Algebra.IsIsoStr`, `IsoAlgebra` (exact recorded full-subcategory specialization).
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; the universe convention is stated
  through the existing native universe choices, with no new metatheoretic object.
- WeilConjectures.WeilSheaf.DerivedHom: `ihomBifunctor`, `derivedHom`;
  WeilConjectures.WeilSheaf.Fourier: `ihomFunctor`.
- WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHom:
  `bifunctorRHomOfComplex`, `bifunctorRHomOfComplexObjIso`, `kInjectiveRep`,
  `kInjectiveRepIso`; WeilConjectures.Algebra.Homology.BifunctorHomComplex:
  `bifunctorHomObj`, `bifunctorHomπ`, `bifunctorHomMapLeft`, `bifunctorHomMapRight`.
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective:
  `rightDerivedFunctorObjQIso`; the Comp module:
  `rightDerivedFunctorNatTrans`, `Adjunction.preservesKInjectiveComplexes`.
- The stated proof-dependency modules are plain imports:
  WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian,
  WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap,
  Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions, and
  WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution.
  Their recorded declarations are respectively
  `SheafOfModules.grothendieckAbelian_with_localized_generator`,
  `CategoryTheory.quasiIso_homComplex_map`,
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions`, and
  `Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`.
  Mathlib's `IsGrothendieckAbelian` and
  `CochainComplex.IsKInjective.Qh_map_bijective` are already exposed by these
  imports/the native models. All proof-dependency modules are retained as the
  plan for stage 3. Their full signatures/docstrings and Stacks 0A95 were read.

Edge cases checked: X empty; A=0; N=0; negative lower bound; an unbounded
K-injective representative with bounded-below cohomology; alpha an identity;
alpha an arbitrary quasi-isomorphism without Mono; a zero source/target arrow;
and changes of both resolutions. The formulas retain each case. In the identity
case the first transport and precomposition are identities. At p=0 the sign
identification is the identity in every degree, including negative degrees.

Searches made with msearch.py:

- leanfinder: "Derived internal Hom from a sheaf in degree zero is naturally
  isomorphic to the right derived functor of internal Hom from that sheaf".
  Eight hits on sheaf global sections/Hom, sheafification and Cartesian closed
  sheaves; no equivariant native resolution comparison.
- loogle: "DerivedCategory.bifunctorRHom,
  CategoryTheory.Functor.rightDerivedFunctor". Zero hits; unknown identifier
  DerivedCategory.bifunctorRHom (it is upstream, not Mathlib).
- grep: "bifunctorRHom.*[Ss]ingle|[Ss]ingle.*bifunctorRHom|bifunctorHom.*[Ss]ingle".
  Zero Mathlib hits.
- leansearch: "The derived internal Hom from a sheaf in degree zero agrees
  naturally with the right derived functor of internal Hom from that sheaf".
  Eight hits: ordinary rightDerived, toRightDerivedZero, rightDerivedZeroIsoSelf
  identities, Ext.mk₀_hom, sheafHom', and the left-exact zero-derived instance.
  None states the native equivariant total-derived comparison.
- rg of WeilConjectures and Sheaf for bifunctorRHom, the single-source
  comparison, derivedHom_single_resolution and singleResolutionProjection;
  grep of WeilConjectures for this node id. The native constructions exist but
  this comparison does not. The existing
  CategoryTheory.derivedInternalHom_single_comparison works with O_X-module
  sheaves in the ordinary ringed-space derived category and a different
  derivedInternalHom construction. Its full signature/docstring were read;
  it is not a statement in the native fixed-pair derived category.

No new nodes, dependency-record repairs, disputed statements, or source-based
statement corrections are needed. The live item is already split and reviewed
at stage 1; this delivery changes only lean and does not resplit it. The earlier
worker's reported stage-1 refusal therefore does not settle this stage-2 task.

Validation: compiled with the prescribed scompile.py in module mode; no errors
or warnings other than the expected declaration-uses-sorry warnings. All variables
and universes are bound explicitly with autoImplicit false. The node copy retains
all original fields verbatim except lean, whose signature is extracted verbatim
from the module. The prescribed dry run and delivery are the remaining gates.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
