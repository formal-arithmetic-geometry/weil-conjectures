## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleModuleDirectImageLeftExact` states
`AlgebraicGeometry.Scheme.proEtaleConstantModuleDirectImage_additive_leftExact`.
Its proof is deliberately `sorry`, as required in stage 2. No definition is added.
The node is unchanged except for its `lean` record.

Hypotheses and clauses:

- Schemes and their morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`; there is no
  quasi-compactness, separation, invertibility or characteristic hypothesis.
- The commutative coefficient ring: `(A : Type u) [CommRing A]`, exactly the
  coefficient/site universe convention of the recorded direct-image definition.
  Universe `u` is explicit. The dependency lifts coefficients to `u+1`, leaving the
  small pro-etale site object universe `u+1` and Hom universe `u` unchanged.
- The functor `f_*` is exactly `proEtaleConstantModuleDirectImage f A`, not the
  module-object condensed-coefficient functor. Its underlying sections and maps are
  precomposition with `proEtaleBaseChange f`, and its scalar action uses the
  canonical `proEtaleCoefficientDirectImageMap f A`.
- Additivity is `(proEtaleConstantModuleDirectImage f A).Additive`.
- Left exactness is `PreservesFiniteLimits (proEtaleConstantModuleDirectImage f A)`.
  In these abelian categories this is equivalent to the node's explicit condition
  on every exact sequence `0 → F' → F → F''`: additivity gives preservation of
  finite biproducts and zero; preservation of such sequences gives preservation of
  kernels; finite biproducts and kernels construct all finite limits. Conversely,
  preserving finite limits preserves kernels and hence those exact sequences.
  No surjectivity at the last term or preservation of cokernels is asserted.

Dependencies read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
  `AlgebraicGeometry.Scheme.proEtaleConstantModuleDirectImage`, including its full
  implementation and docstring. Its recorded direct-image dependency now has an
  exact existing record, so the previous wait is resolved.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`, `SheafOfModules`, and
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`, `SheafOfModules.instAbelian`,
  are the original Mathlib match for the proof dependency
  `def-weil-sheaf-of-modules-category`. The imported inverse-image module also
  imports that node's `Sheaf.CategoryTheory.RingedSiteModules` wrapper; neither a
  new module category nor a duplicate abelian structure is introduced.
- `Mathlib.CategoryTheory.Limits.Preserves.Finite`, `PreservesFiniteLimits`, is the
  standard categorical expression of left exactness.

Sources read: the blueprint `def-weil-derived-direct-image`, first paragraph;
Stacks `sites-modules.tex`, section-kernels and lemma-exactness-pushforward-pullback
(Tags 03DA/03DC); and `coord/pefw-upstream-framework.md`. The declaration docstring
records the node's full sectionwise-addition/kernel proof plan, including scalar
compatibility and the exact-sequence/kernel identification.

Edge cases: arbitrary morphisms and schemes, including the empty scheme; the zero
ring; zero module sheaves and zero arrows; identity morphisms; and the empty finite
limit (the terminal/zero object). No nonempty, nontrivial, reduced or positive-degree
condition is added. Finite limits are the usual finite diagrams, with no independent
site-size constraint. The dependency's existing coefficient-size convention is
retained.

Searches for an exact existing theorem (all found only general constructions):

- `msearch.py leanfinder`, query: "Direct image of sheaves of modules on small
  pro-etale sites is additive and preserves finite limits". Eight hits, including
  `SheafOfModules.instPreservesFiniteLimitsSheafAddCommGrpCatToSheaf`, forgetful
  functors, sheafification, evaluation, and condensed-module constructions; none
  is the required pro-etale module direct-image assertion.
- `msearch.py loogle`, query: `SheafOfModules.pushforward, Functor.Additive`:
  zero hits, with note "unknown identifier 'Functor.Additive'". The earlier valid
  query `SheafOfModules.pushforward` returned the generic pushforward, composition,
  congruence and adjunction constructions, not the asserted theorem.
- `msearch.py grep`, query:
  `pushforward.*[Aa]dditive|[Aa]dditive.*pushforward|preservesFiniteLimits`,
  subdirectory `Algebra/Category/ModuleCat/Sheaf`: five hits, all in `Limits.lean`,
  about the generic forgetful/evaluation infrastructure.
- Direct `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  `/home/ubuntu/weil-newtargets-NG/lean/Sheaf` for the canonical functor name and
  item id: only the dependency definition; no existing statement. The separate
  project search for additive/pro-etale finite-limit assertions found other
  inverse-image and open/closed functors, not this assertion. Read the generic
  Mathlib pushforward implementation to confirm its sectionwise action.

Validation: the prescribed `scompile.py NG
lem-weil-proetale-module-direct-image-left-exact` compiled the sandbox module and
its library-path version cleanly, without warnings or errors. The only postponed
proof is the named theorem matched by this DAG node. No statement fault or
STATEMENT-DISPUTED issue was found.

## Second reading by NG

I independently read the item JSON, its blueprint source paragraph, Stacks
sites-modules.tex (03D7, section-kernels, 03DA and 03DC), both dependency nodes,
and the actual dependency implementations. No statement correction, new node,
or dependency module is needed. The Lean file and its verbatim lean.statement
record are unchanged.

Object/hypothesis/conclusion checklist (H3):

1. Schemes X and Y: `{X Y : Scheme.{u}}`. Pass: arbitrary schemes, not affine,
   Noetherian, nonempty, separated, or schemes over a fixed field.
2. Scheme morphism f: `(f : X ⟶ Y)`. Pass: no property of f is assumed.
3. Commutative coefficient ring A: `(A : Type u) [CommRing A]`. Pass: this is
   precisely the recorded small-site/coefficient convention of the dependency,
   with no finiteness, torsion, characteristic, or nontriviality requirement.
   A larger coefficient ring and smaller schemes are covered in a common larger
   universe; no new equality of site object and Hom universes is imposed.
4. Categories of module sheaves: the source and target of
   `proEtaleConstantModuleDirectImage f A` are `SheafOfModules.{u+1}` over the
   ring-forgotten `proEtaleConstantRing X A` and `proEtaleConstantRing Y A`.
   Pass: ProEtaleInverseImage.lean:237 uses exactly the dependency node's
   base-change functor and coefficient structure map. I read that definition,
   `proEtaleBaseChange`, `proEtaleConstantRing`, and
   `proEtaleCoefficientDirectImageMap`, and the underlying Mathlib
   `SheafOfModules.pushforward` implementation. The functor evaluates on
   V times_Y X, restricts scalars through rho, and acts by the original linear
   components. It is not the condensed-module-object functor. The site objects
   remain in u+1, morphisms in u, and modules in u+1.
5. Additivity: `(proEtaleConstantModuleDirectImage f A).Additive`. Pass: it
   asserts preservation of sums of morphisms in the recorded preadditive
   categories; zero morphisms follow as in proof step 1.
6. For every exact sequence beginning with zero, its image is exact:
   `PreservesFiniteLimits (proEtaleConstantModuleDirectImage f A)`. Pass by
   equivalence, not a stronger conclusion: in these abelian categories an
   additive functor preserving kernels preserves finite limits, since it
   preserves finite biproducts and equalizers are kernels of differences.
   Conversely finite limits preserve kernels and the zero object. Any exact
   sequence 0 -> F' -> F -> F'' is a kernel fork up to its unique isomorphism,
   so its image is exact. Applying the node's assertion to every kernel fork
   recovers preservation of kernels and hence finite limits. There is no
   final surjectivity condition. The universal quantification over sequences
   is thus retained. I also checked Mathlib's definition of
   `PreservesFiniteLimits` and its higher-universe finite-shape instance.

The module-category dependency is the existing Mathlib `SheafOfModules` and
`SheafOfModules.instAbelian`: I read the object, linear-morphism, category, and
abelian declarations in Sheaf.lean and Sheaf/Abelian.lean. The imported
RingedSiteModules wrapper publicly imports the latter; the direct-image
module imports the pro-etale size convention. No extra sheafification instance
is required as a theorem hypothesis. Stacks 03DC assumes only a morphism of
ringed topoi. Although the blueprint applies this fact to finite-level rings
and schemes with ell invertible, Stacks proves exactly the generality in the
node; those application-specific hypotheses are unnecessary here.

Edge cases: the empty scheme and identity morphisms are admitted by the
scheme binders. Zero sheaves, zero maps, and the zero coefficient ring are
admitted. The empty finite diagram (terminal/zero object) is included in
finite-limit preservation. There is no degree n or index family in the
statement, hence no positivity or inhabited-index assumption; all ring
characteristics are covered. The universe u is declared and every variable
is explicitly bound. The dependency's ULift coefficient construction retains
all the ring data.

Independent H4 searches, using different queries from the first reading:

- `msearch.py ... loogle 'SheafOfModules.pushforward, "limit"'`: zero hits.
- `msearch.py ... leanfinder 'Direct image on modules over a sheaf of rings
  preserves finite limits and sums of morphisms'`: eight hits, concerning
  module sheafification, forgetful functors, finite limits in the module
  category, preadditivity, and restriction of scalars. None states this
  pro-etale direct-image assertion.
- `msearch.py ... leansearch 'Direct image of module sheaves is left exact'`:
  service unavailable (Internal Server Error); recorded as unavailable,
  not as evidence of absence.
- Direct rg in both project Lean roots and the older upstream WeilConjectures
  root for `proEtaleConstantModuleDirectImage` and pro-etale additive/left-exact
  variants finds only the canonical definition. Broader kernel/additivity
  searches find general tools and the separate etale theorem, not this
  assertion. The Mathlib PushforwardContinuous.lean definition and searches
  for pushforward/additivity/finite-limit assertions give constructions and
  adjunction machinery, not an exact existing theorem for this functor.

H5/H6/H8/H9: no definition or proof is added. The sole postponed theorem is
this node's named theorem. Its docstring includes the source and blueprint id
and all three proof steps: componentwise addition, sectionwise kernels with
rho-linear scalar compatibility and preservation of zero, then transport of
the kernel identification for an arbitrary left exact sequence. The imports
already expose the statement and proof dependencies. Naming, line lengths,
namespace, and explicit universe conventions are correct. There is no local
notation, private construction, hidden let-binder, or unbound variable.

Mismatches found: none. Changes made: this independent second-reading report
and search evidence only; the correct Lean statement was left intact.

Second-reader validation: scompile.py compiled both the sandbox module and its
library-path version cleanly (1.6 s and 1.7 s), with no errors or warnings.
