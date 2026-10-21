## Worker report

Module `Sheaf.Paper.SignedLineScalarPullbackSquare` states
`SheafOfModules.existsUnique_signedLineScalarPullbackSquare`. Its only theorem has
proof `sorry`. Two fully written Prop-valued helpers express the node's own normalization
and its scalar/pullback square. There is no new tensor, internal Hom, scalar extension,
pullback functor, signed power, or chosen reassociation isomorphism.

Clause-by-clause correspondence:

- Sites: `C D : Type u`, `Category.{v}`, `J`, `K`; the theorem has
  `HasFiniteLimits C`, `HasFiniteLimits D` (including final objects),
  `PreservesFiniteLimits U`, and `_hcover : CoverPreserving J K U`.
  `U.IsContinuous J K` is the conventional sheaf-pushforward interface for this
  finite-limit- and covering-preserving functor. Object, morphism and ambient
  coefficient levels remain independent: `u`, `v`, `w`; coefficients and modules
  live in `max u v w`. The sheaf-composition/sheafification/local-equivalence
  instances are the existing infrastructure on these small-relative-to-coefficient
  sites, including slices for the scalar-tower normalization. No equality of site
  object and morphism universes is imposed.
- Four commutative ring sheaves are `R S : Sheaf J CommRingCat` and
  `R' S' : Sheaf K CommRingCat`; `ι` and `ι'` are their given maps.
  `a : R → u_*R'` and `b : S → u_*S'` are the adjoints of the node's
  structural maps from inverse images. They are RingCat sheaf morphisms between
  the forgotten commutative ring sheaves, hence preserve 0, 1, addition and
  multiplication. `_hab` is precisely `b f⁻¹(ι) = ι' a` under adjunction.
- The node's `F_R`, `F_S` are the existing `ringedSitePullbackFunctor` at `a`, `b`,
  with the proved `module_pushforward_isRightAdjoint_of_universes` supplying their
  existence. They are Mathlib's actual left adjoints of the structural-map-induced
  module pushforwards. The tensor formula in the node is the same left adjoint,
  with its canonical unit; no freely chosen functor is an assumption.
- `L N L' N'` are the four module sheaves, in the recorded `ringedSiteModules`.
  `_hL`, `_hN`, `_hL'`, `_hN'` each assert a `CoversTop` family on which the
  module restricted to the slice is isomorphic to the corresponding ring unit.
  This is exactly local freeness of rank one on a cover of the final object.
- `c c' p q` are exactly the four given line isomorphisms. `_hc` asserts the
  specified degree-one square, using `SignedLineScalarPullbackSquare`.
- All four integer powers are the dependency's `signedLinePower.{u,v,w}`:
  degree zero is its ring unit, positive degrees are `scalarTensorPower`, and
  negative degrees are the recorded `homObj` of the positive power into the unit.
- `B` and `B'` are the given `c_m` and `c'_m`. `_hB` and `_hB'` are exactly
  `SignedLineComparisonNormalized`, imported from the scalar-tensor-tower node;
  this fixes unit, degree one, positive tensor recursion and the evaluation dual.
- The conclusion is `∃! PQ` in the product of the two types of integer-indexed
  isomorphism families. `PQ.1` and `PQ.2` are the required `p_m` and `q_m`.
  The first two conjuncts impose `SignedLinePullbackNormalized` separately.
  That helper's first conjunct fixes the coefficient-unit map by its value on
  every unit image of every coefficient section. Its second is `(P 1).hom = p.hom`.
  Its third gives positive tensor recursion on every pair of local sections.
  Its last gives negative evaluation on every pulled functional and positive
  section, with coefficient image `a(φ(x))`. The same helper applied to `b` gives
  the other evaluation identity. Because the positive map is invertible, the
  evaluation equation specifies exactly transpose followed by precomposition
  with its inverse. It does not assume a general internal-Hom comparison is invertible.
- The final conjunct asserts the scalar/pullback square for `∀ m : ℤ` using
  `(B m)`, `(B' m)`, `(PQ.1 m)`, `(PQ.2 m)`. No sign or degree is omitted.
- There are no flatness, nonzero-ring or invertibility hypotheses on `a b ι ι'`.

Why the generator equations are full morphism equations: the square's left source
is `F_S(L tensor_R S)`. Pullback adjunction detects equality by its values on the
unit images of ALL local sections of `L tensor_R S`; scalar-extension adjunction
and sheafification detect those maps by `scalarExtensionSection ι L V s x`.
The canonical reassociation carries that generator to
`scalarExtensionSection ι' (F_R L) (u V) b(s) (unit_a(x))`.
Applying scalar extension of `p` and then `c'` yields exactly the right side of
`SignedLineScalarPullbackSquare`. Multiplication by arbitrary target scalars follows
from S'-linearity. Neither sectionwise surjectivity of sheafification nor enough
points is used. This gives precisely the displayed categorical square under the
node's canonical reassociation; it introduces no unspecified comparison data.
Similarly positive recursion and negative evaluation are equations of bilinear
sheaf pairings detected on their canonical adjunction-unit generators. In the
negative equation, testing all source objects includes every source restriction;
the localized adjunction detects equality on all target-slice arguments. This is
the same uniqueness mechanism as `exists_pullback_pairing_transfer`.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`,
  the structural-map and induced-module-action convention. Here its ring maps are
  in their adjunct presentation for the given site functor; no second notion is defined.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and its public
  site-tensor API: `cochainModulesMonoidal`, `siteSheafTensorTmul`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, the actual slice sheaf Hom, used through signed powers.
- `Sheaf.Paper.SignedLineScalarTensorTower`: `signedLinePower`,
  `SignedLineComparisonNormalized`, and the seven theorem clauses providing the
  scalar comparisons, dual evaluation and tower normalizations. Its underlying
  scalar API is `changeOfRingsOfUniverses` and `scalarExtensionSection`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the recorded site convention;
  topological sites here use Mathlib `GrothendieckTopology` and `CoversTop`.
  `def-weil-size-convention` is a metatheoretic convention, rendered by the explicit
  independent universes and their common bound, as its record instructs.
- Proof imports are `Sheaf.CategoryTheory.SiteInverseImageTensor`
  (`CategoryTheory.siteInverseImage_tensor`),
  `Sheaf.CategoryTheory.ModulePullbackTensorIso` (`module_pullback_tensor_iso`),
  `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
  (`module_pullback_pushforward_adjunction`),
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback`
  (`finite_free_dual_pullback`, `ringedSitePullbackFunctor`,
  `ringedSitePullbackSection`), and
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackLocalizationOfUniverses`
  (`RingedSitePullback.localComparison_eq` and the unit-compatible localization).
  Their specified tensor, unit and evaluation normalizations give the proof route
  carried in the theorem docstring. `PullbackExistsOfUniverses` supplies the proved
  existence theorem used explicitly rather than making adjoint existence an assumption.

Sources opened: the current blueprint `prop-weil-twist-preserves.proof.md` in
main-20261015, and Stacks `sites-modules.tex`, `remark-pullback-internal-hom`
(Tag 0GMX), including its local-slice definition of the pullback Hom map.
No mathematical statement correction or dependency repair was required.

Edge cases checked on the statements: degrees 0, 1, -1 and all negative degrees;
identity ring maps; arbitrary nonflat maps such as Z → Z/2 on the point site;
zero coefficient rings (the ring unit may itself be zero, with no excluded case);
empty covering families when the topology permits them (no Nonempty/Nontrivial
assumption); independent site object/morphism bounds. The positive recursion starts
at n+2 with n : ℕ, leaving degree one prescribed rather than repeating a unit factor.
The negative case uses `Int.negSucc n`, so n=0 covers degree -1. On a point-site
basis, if p and q multiply by units λ and μ, the normalization forces λ^n and μ^n
in positive degree and their inverse powers in negative degree, exactly as required.

Searches actually run (msearch log is in the sandbox):

- LeanFinder: "A commutative square of ringed site pullbacks and line scalar
  comparisons commutes on every signed tensor power including duals" — 8 hits,
  including pullbackObjFreeIso naturality, pullbackComp conjugacy and pullback_assoc;
  none states the signed square for four line sheaves with arbitrary coefficient maps.
- Loogle: "SheafOfModules.pullbackComp, SheafOfModules.pullbackObjUnitToUnit" — 0 hits.
- Mathlib grep through msearch: "pullback.*(dual|tensor)|baseChange.*(dual|tensor)"
  in `Algebra/Category/ModuleCat` — 0 hits.
- LeanSearch: "Naturality of signed tensor power scalar comparisons under a morphism
  of ringed sites without flatness" — 8 hits, including general module naturality,
  pushforward natural transformations, flat tensor finite limits and RingHom.Flat;
  none is the item.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for signedLine,
  signed/pullback, pullback/scalar and the exact node ID: found the scalar-tower
  dependency and other scalar-route material, no existing statement of this item.
  Mathlib PullbackFree and PullbackContinuous were read, as were the recorded
  project dependency signatures and docstrings. The existing derived signed-line
  base-change material does not cover the node's arbitrary noninvertible ring maps.

Validation: server single-file compilation through the prescribed scompile.py;
initial module compiled cleanly in both sandbox and library naming modes. All
variables/universes are explicit (`autoImplicit false`), every line is at most 100
characters, and the only postponed proof is the item's named theorem. The report
and final import set are also checked by the prescribed delivery dry run.

## Second reading by Q57

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
