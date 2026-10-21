## Worker report

The delivery states `CategoryTheory.RingedSiteIdeal.sheaf_tensor_ideal_quotient` in
`Sheaf.Paper.SheafTensorIdealQuotient`. Its only postponed proof is this theorem's `sorry`.
The supporting definition module has real data throughout, with no postponed theorem,
axiom, arbitrary map, or object chosen from an existence theorem. The item's statement,
proof and proof dependencies are unchanged. Its statement dependencies gain the new
construction node described below. No dependency record is repaired.

Source read: `literature/stacks-project/sites-modules.tex`, Tag 03EK,
`section-tensor-product` (the sectionwise tensor and its sheafification), and Tag 03CY,
`lemma-sheafification-presheaf-modules` (module sheafification, action and adjunction).
The extra quotient identification and naturality calculations are the item's own
nine-step proof, all of which are reproduced in the theorem docstring. The dependency
source signatures and docstrings were read, including the existing RingedSiteIdeal
interface and its local membership condition. There is no repair-note file for this item.

Hypotheses and clauses, matched to Lean:

- A small site and a commutative ring sheaf are `{C : Type u} [SmallCategory C]`,
  `{J : GrothendieckTopology C}`, and `(R : Sheaf J CommRingCat.{u})`. The site and
  coefficients are placed in the common value universe used by the item's proof.
  There is no assumption of points, pullbacks in C, a basis/pretopology, or flatness.
- Ideal subsheaves are the existing `RingedSiteIdeal R`, whose `sections`, `restriction`,
  and `local_mem` fields encode exactly the ideals, restrictions, and local membership.
  Module sheaves and linear morphisms are the existing `SheafOfModules` category.
- `localProduct I F` is a concrete intersection of all restriction-stable submodule
  families that have local membership and contain each sectionwise ideal product.
  The first conclusion asserts its associated module presheaf is a sheaf. The next
  conclusion identifies its sections with precisely the local finite sums in the node:
  `∃ S : Sieve U, S ∈ J U ∧ ∀ V g, S g → ∃ n i x, ... = ∑ k : Fin n, (i k).val • x k`.
  `n = 0` is allowed; the local number of summands can vary on the covering sieve.
- `ringQuotientPresheaf I` has the actual rings `R(U) / I(U)` and their induced
  restrictions. `ringQuotient I` is its CommRingCat sheafification; `ringProjection I`
  is the sectionwise projection followed by the sheafification unit. It is not assumed
  to be surjective on the sections of each object.
- `moduleQuotientPresheaf I F` is the cokernel of the actual inclusion
  `(localProduct I F).ι` in presheaves of modules. Mathlib's evaluation functors
  preserve cokernels, so this is exactly the sectionwise quotient F(U)/IF(U), up to
  its canonical cokernel identification, not a quotient formed in sheaves prematurely.
  `moduleQuotient I F` applies the recorded module-sheafification functor to it.
  `moduleProjection I F` composes the actual cokernel projection and sheafification unit.
- `quotientCoefficient I` is S as an R-module by the recorded restriction functor.
  `quotientTensor I F` is the existing `monoidalCategory R` tensor of F and that
  coefficient sheaf. Pure sections are exactly the recorded `RingedTensor.pure`.
- The existential family `a I F` consists of R-linear isomorphisms from that actual
  tensor to the already constructed quotient. `Q I F` is an S-module sheaf and
  `e I F` identifies its restricted R-module with the fixed quotient. This is how the
  canonical S-action on that fixed object is expressed without changing its underlying
  abelian sheaf. The R-linearity of e makes the action extend multiplication by r on
  quotient representatives. Its uniqueness follows from local lifts along R→S and q.
- The pure-section clause is exactly `a(pure(f, π(r))) = q(r • f)`. The inverse clause
  is exactly `a.inv(q(f)) = pure(f,1)`. Thus the formulas apply to images of local
  sections in the sheafifications, not to falsely assumed global representatives.
- S-linearity is the explicit clause
  `e.inv(a(pure(f,s*t))) = s • e.inv(a(pure(f,t)))` for arbitrary sections s,t of S.
  The action on the tensor multiplies the second factor. Additivity, local generation
  by pure tensors, and separatedness extend this equality to the entire tensor;
  conversely an S-linear comparison satisfies it. An invertible additive S-linear map
  has S-linear inverse, so this expresses an S-linear isomorphism. `@id` only exposes
  the existing Q section type to instance inference and does not change the object.
- `uMap I F` is a sheaf morphism explicitly normalized by the clause
  `uMap(f) = pure(f,1)` on every section. Thus it is the specified map, not an
  unconstrained arrow. The next clauses are `uMap ≫ a.hom = moduleProjection`,
  `Epi uMap`, and the sectionwise kernel equivalence
  `uMap(f) = 0 ↔ f ∈ (localProduct I F).obj W`. Kernels in this category are sectionwise.
- For every R-linear `h : F ⟶ G`, `qh` is the induced quotient map, characterized by
  `q_F ≫ qh = h ≫ q_G`. The existence of `hS : Q I F ⟶ Q I G`, with the displayed
  restriction square through e, makes this induced map S-linear. The final equation
  is `a_F.hom ≫ qh = tensorHom h (𝟙 _) ≫ a_G.hom`, exactly module naturality.
  The quotient-projection normalization determines qh uniquely because q is epic.
- `IsContained I' I` means `∀ U, I'.sections U ≤ I.sections U`. `ringTransition hI`
  is the sheafification of the actual ring quotient transitions. `tM` is normalized
  on every S' section by `tM(s) = (ringTransition hI)(s)`, so is precisely t restricted
  to R-modules. `v` is normalized by `q_I' ≫ v = q_I`. The remaining equations are
  `a_I'.hom ≫ v = tensorHom (𝟙 F) tM ≫ a_I.hom` and
  `u_I' ≫ tensorHom (𝟙 F) tM = u_I`, exactly the two ideal-inclusion squares.
  These morphisms and equations are all in the R-module category, as in the node.

The simultaneous families over all I and F package the individual canonical comparisons
and their two naturalities. Classical choice of this family adds no mathematical
hypothesis. No definitions choose data from this theorem. No clause is suppressed and
no correction to the item's mathematical statement was needed.

Dependency declarations used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` is the
  transparent abbreviation for the `SheafOfModules` used here. The original Mathlib
  category, its linear morphisms, and its sectionwise kernels are retained.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification` and `sheafificationAdjunction` construct Q and q;
  the module-sheafification interface leaf uses the same functor with a presheaf
  coefficient ring and its sheafification map.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` retains the existing localization tensor.
  The direct tensor expressions select `SheafOfModules.monoidalCategory R` explicitly.
- `Sheaf.Paper.RingedTopoiTensorSections`: `RingedTensor.pure`, `ringSheaf`,
  `restriction`, and the pure-section restriction/naturality/extensionality theorems.
- `Sheaf.Paper.RingedSiteIdeal`: `RingedSiteIdeal` and `siteModuleRings`; no copy of
  the ideal notion is introduced.
- Proof imports: `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
  (`CategoryTheory.sheafification_sections_local`) and
  `Mathlib.CategoryTheory.Sites.PreservesSheafification`
  (`sheafifyComposeIso`, `sheafComposeIso_hom_fac`, concrete forgetful compatibility).
  The proof uses covering-sieve local representatives; the theorem's statement does
  not inherit the stronger precoverage/pullback hypotheses of one available lemma.

Edge cases checked mathematically: I=0 gives IF=0 and the unit comparison; I=R gives
IF=F and the zero quotient. F=0, R the zero ring, and an empty category are permitted.
Empty covering sieves and zero-term sums are permitted. I'=I gives identity transitions;
I'=0 is permitted. A one-object site recovers the ordinary tensor quotient lemma,
including non-flat modules such as Z/2 over Z. A site with quotient sections that have
only local lifts is covered because all quotients are sheafified and every formula is
stated on images, while the S-linearity and tM clauses also quantify over arbitrary
quotient-ring sections. No common-refinement argument requires fibre products.

Searches actually run with msearch.py:

- LeanFinder: `For a sheaf of modules F over a commutative ring sheaf R and ideal
  subsheaf I, tensor F with R/I is naturally isomorphic to F/IF`: eight ordinary-module
  tensor quotient hits, including `TensorProduct.tensorQuotEquivQuotSMul` and its
  projection/inverse formulas. No general sheaf isomorphism or naturality statement.
- Loogle: `TensorProduct.tensorQuotEquivQuotSMul`: six hits for that ordinary-module
  equivalence and its section formulas. These do not handle sheafified quotient rings.
- LeanSearch: `sheaf tensor product quotient ideal sheaf module`: eight ordinary
  tensor/ideal quotient hits, no exact sheaf statement.
- Mathlib grep: `quotient|ideal` in `Algebra/Category/ModuleCat/Sheaf`: no hits returned
  by the wrapper. A separate direct read/search found the general Submodule, colimit,
  module sheafification and tensor interfaces, which are reused.
- The additional three construction searches are recorded with their actual outputs
  in the new node's `mathlib_searches`. They found ordinary quotients, tilde modules,
  and the existing module-sheafification action, but no such general quotient package.
- `rg` over WeilConjectures and Sheaf found RingedSiteIdeal and the private rank-one
  quotient helper in RingedIdealQuotientComparison; the latter does not define arbitrary
  F/IF or a commutative ring quotient sheaf. Searches for the item id in
  WeilConjectures, the upstream-name index, and the proposed declaration names found
  no match. DAG searches found the existing ringed-site ideal node but no node owning
  these arbitrary-module quotient constructions. `blueprint_refs.py search
  'ideal quotient'` returned zero blueprint nodes; `ancestor` returned
  `def-weil-pbc-completed-pullback`.

Validation: all compilation uses scompile.py, with both modules supplied in dependency
order against the published live library. The definition module compiled cleanly.
The theorem elaborated successfully after exposing the coefficient unit and Q action
section types; two long lines were then wrapped and the clean compile was rerun.
There is no STATEMENT-DISPUTED flag or mathematical node fault.

## New nodes

`def-weil-pbc-ideal-module-quotients` owns the canonical local ideal product, its
sectionwise module cokernel and sheafification, ring quotient presheaf and sheafification,
quotient projections, ideal-inclusion quotient transitions, quotient coefficient module,
and existing sheaf tensor specialization. Its source is Stacks 03CY and 03EK, with the
item's explicit quotient prescription. Its definitions use real intersections, actual
Mathlib cokernels, actual quotient rings, and actual sheafification units. Searches in
Mathlib, WeilConjectures, Sheaf, the DAG and the full blueprint found no existing node or
public declaration with these constructions. It reuses the existing ideal node and all
four relevant original interfaces instead of copying any of them. The theorem proves
that the intersection construction has exactly the specified locally finite-sum sections.
The item directly cites this new node. There are no new proof nodes or dependency modules.

## Second reading by ND

A separate second pass reread the item statement, each definition, and the full theorem
signature. The dispatcher forbids starting another agent, so this records the worker's
second pass; the maintainer supplies the independent review.

I checked that localProduct is a submodule of the actual F.val, that its quotient is
sheafified after the sectionwise cokernel, and that the ring quotient is independently
sheafified as commutative rings. The tensor is F⊗S in the correct order; it is not the
left-ordered extension-of-scalars object. Pure sections are the recorded existing pure
sections, including the comparison from sheafification. The isomorphisms have the
correct direction, and the inverse formula uses the actual q(f). The S-action and
S-linearity clauses are tied to the quotient via e, so cannot describe an unrelated
module. Module naturality uses tensorHom h id; ideal naturality uses tensorHom id tM.
All projection, comparison and unit squares have the intended order of composition.
Both existential quotient maps are normalized on their projections, and tM is fixed on
all S' sections by the actual ringTransition. The small-site and coefficient universes
are explicit. Every variable and universe is bound, and no file-local notation, private
definition, or instance is introduced. The only changes found necessary in this reading
were explicit types for the unit section and for the existing Q scalar action, and line
wrapping to remove the style warnings. The node's mathematical statement was unchanged.
