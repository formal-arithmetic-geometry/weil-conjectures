## Worker report

Module: `Sheaf.Paper.FiniteOrderedFlasqueCechComparison`; declaration:
`AlgebraicGeometry.finiteOrderedFlasqueCechComparison`. This stage states one theorem,
with its entire proof `sorry`; it defines no new objects. The existing finite ordered
Čech construction is reused, and its landed node
`def-sc-alternating-cech-total-complex` is added to `stmt_deps`.
No statement correction or new definition node is needed.

Hypothesis and conclusion correspondence:

- Scheme X: `(X : Scheme.{u})`, using Mathlib's scheme category.
- O_X-module F: `SheafOfModules.{u} (moduleRings X.toRingedSpace)`, precisely the
  Mathlib category underlying the dependency's `ringedSiteModules` abbreviation.
- Nonnegative cochain resolution and augmentation: `G : CochainComplex ... ℤ`,
  `[G.IsStrictlyGE 0]`, `e : (HomologicalComplex.single ... (.up ℤ) 0).obj F ⟶ G`,
  and `[QuasiIso e]`. The single complex's term in degree zero is definitionally F,
  so `e.f 0` is the required map F → G^0.
- Every G^q has flasque underlying abelian sheaf: `hfl : ∀ q : ℕ,
  TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf ...).obj (G.X (q : ℤ)))`.
  Negative degrees are zero by the nonnegativity hypothesis.
- Finite indexed open cover, including empty: `(r : ℕ) (V : Fin r → X.Opens)` and
  `(hcover : iSup V = ⊤)`, without a positivity hypothesis on r.
- Nonempty subsets and their intersections: an increasing embedding
  `t : Fin (p+1) ↪o Fin r` uniquely enumerates a subset of cardinality p+1.
  `alternatingCechIntersection V t` is its intersection. Quantification over all
  p and t covers exactly every nonempty subset, without repeated indices.
- Section augmentation on every intersection is a quasi-isomorphism: `hsections`.
  Its functor is forget to module presheaves followed by evaluation at the
  intersection, mapped to complexes; its value on the single complex is the
  single complex of sections. This is definitionally Mathlib's evaluation functor,
  spelled as its composite so its additive instance is available.
- L and its alternating restriction differential: `(alternatingCechModuleFunctor V).obj F`.
  It is the product of sections indexed by increasing tuples, with signed deletion
  faces, extended by zero to negative Čech degrees.
- D, its commuting differentials, first quadrant and total signs:
  `(alternatingCechDoubleFunctor V).obj G` and `(alternatingCechTotalFunctor V).obj G`.
  The imported construction puts Čech degree first and resolution degree second;
  totalization is Mathlib's `d_h + (-1)^p d_v`. The Čech functor vanishes in negative
  degrees, while `[G.IsStrictlyGE 0]` gives vertical nonnegativity.
- Alpha is the actual existing `alternatingCechAugmentationMap V G`: restriction
  into the p=0 summand, with no unspecified choice. The first conjunct states
  `QuasiIso` of this map.
- Beta: `∃ β : L ⟶ Tot(D)`, with **every** integer-degree component fixed as
  the Čech map of `e.f 0` followed by the `(n,0)` total inclusion. This specifies
  exactly the canonical q=0 map, and implies its uniqueness. The following
  conjunct is `QuasiIso β`. No object is chosen from an existence theorem.
- Degree-zero agreement: the displayed equality composes global sections of
  `e.f 0` with `alpha.f 0`, and equates it to `alternatingCechZero V F ≫ β.f 0`.
- Scheme-morphism naturality: the final universal quantifier binds Y, h:Y→X,
  F', its nonnegative resolution G', quasi-isomorphism e', the O_X-linear
  coefficient map `u : F ⟶ (Scheme.Modules.pushforward h).obj F'`, and cochain
  map v into the pushed-forward G'. The implication hypothesis is precisely
  augmentation commutativity in degree zero; other degrees of a single complex
  are zero. Beta' again has every component specified. The beta and alpha squares
  use the existing functor maps applied to u and v, respectively.
- This last clause uses the **pushforward presentation** of the inverse-image
  cover complex. `Scheme.Modules.pushforward_obj_obj` identifies sections over
  V_S with sections of F' over h inverse V_S; `pushforward_obj_presheaf_map`
  identifies all restrictions. Inverse image preserves these finite intersections.
  Therefore its tuple terms, face maps, resolution differential and total inclusions
  are exactly those of the inverse-image indexed cover, after restriction of global
  scalars. The target is never an arbitrary complex supplied in place of the specified
  Čech construction. No inverse-image functor on modules or exactness is assumed.
- Coefficient maps are h=identity (using the canonical pushforward-identity iso).
  Open restrictions are the case of the open immersion, with its inverse-image
  indexed cover. There is no flatness binder. The theorem applies separately to
  Y with its cover to obtain the two quasi-isomorphisms there when its flasqueness
  and section-augmentation hypotheses hold. Those hypotheses are intentionally
  unnecessary for the naturality squares themselves.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, a
  transparent abbreviation of the used `SheafOfModules`; read also Mathlib's object,
  linear morphism and evaluation definitions in ModuleCat/Sheaf.lean.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; the present cochain-level statement uses their underlying
  `CochainComplex` and `QuasiIso`, not the localization.
- `Mathlib.Topology.Sheaves.Flasque`: `TopCat.Sheaf.IsFlasque`, the abbreviation of
  the presheaf condition requiring every restriction to be epi. For abelian groups
  these are precisely surjective maps.
- `Sheaf.CategoryTheory.DoubleComplexTotal`: the recorded Mathlib
  `HomologicalComplex₂`, `total`, and `ιTotal`, with the specified signed total.
- `Sheaf.AlgebraicGeometry.AlternatingCechTotalComplex`: read the full module's
  definitions of intersection, tuple terms, signed differential, module presheaf,
  module complex functor, double functor, total functor and alpha augmentation.
- Proof-only import `Sheaf.Algebra.Homology.FirstQuadrantTotalComparison`:
  `HomologicalComplex₂.quasiIso_totalMap_of_columns`; its explicit flipped-component
  hypothesis and full docstring were read. This is the node's total comparison tool.

Edge cases checked: r=0 forces X empty by hcover, all tuple types are empty, and
sections of the empty scheme vanish. No `Nonempty` hypothesis excludes this case.
Empty intersections give zero section objects by the sheaf condition. For r=1
only the singleton Čech column survives. For p≥r the product is empty and zero.
At n=0 both maps have precisely the stated singleton components, and for n<0
all coefficient Čech terms vanish. The resolution has no upper bound: each total
first-quadrant diagonal is finite. Zero coefficients are allowed. No characteristic,
flatness or nonempty-scheme assumption is present. All variables and the universe
are explicitly bound, with auto-implicit disabled by the server compiler.

Searches (2026-10-15):

- msearch.py leanfinder: "Finite ordered Cech complex comparison with a flasque
  resolution quasi isomorphisms". Eight generic quasi-isomorphism, CM5b,
  injective-resolution and derived-fraction results; no matching theorem.
- msearch.py loogle: `"cechComplex"`. One `CategoryTheory.cechComplexFunctor`
  hit, the usual (all tuples) construction; not this finite ordered flasque comparison.
- msearch.py grep: `flasque|cechComplex` in Topology/Sheaves. Five hits in
  Flasque.lean defining flasqueness and its basic properties, not this statement.
- rg in Mathlib: `finiteOrderedFlasqueCechComparison|ordered.*flasque|flasque.*ordered`:
  no matches. Read the existing Mathlib flasque and bicomplex declarations.
- rg in WeilConjectures: ordered Čech search found MonomialCech.lean and
  Cohomology/Affine/Cech.lean; their special affine/monomial comparisons do not
  state this result. Exact node-id search has no hits. Flasque search finds
  InjectiveFlasque and derived-direct-image material, without this theorem.
- rg in lean/Sheaf found the general `AlternatingCechTotalComplex` construction,
  which is reused. PrincipalCechBicomplexComparison is affine/principal and
  AbelianCechComparisonConstruction uses injective resolutions and usual tuples;
  neither states this theorem. Exact declaration-name and flasque/Čech combined
  searches in lean/Sheaf, WeilConjectures and dag/lean_names_upstream.json returned
  no matching declaration.

Validation: all compilation uses scompile.py on the server, nice 19, two threads,
60 seconds per file. The final module compiled with no errors or warnings (3.2 s).
The section evaluation functor was unfolded into its additive composite to resolve
an instance elaboration issue; this changes no mathematical object or hypothesis.


## Second reading by NH

Independent reading of the repository node, sandbox node and module, dependency
signatures and constructions, and the actual Stacks cohomology.tex source.
No mathematical mismatch found. The Lean and node signature are unchanged;
this reading adds the independent review documentation only.

Object, hypothesis and conclusion checklist (each verdict: matches):

1. A scheme X: `X : Scheme.{u}`. Read Mathlib Scheme and Scheme.Hom;
   no base field, separation, Noetherian or nonemptiness condition is imposed.
2. An O_X-module F: `SheafOfModules.{u} (moduleRings X.toRingedSpace)`.
   Read `ringedSiteModules` and Mathlib SheafOfModules, Hom, forget,
   evaluation and toSheaf. The abbreviation is precisely this category;
   objects are module presheaves with the abelian sheaf condition and maps
   are sectionwise linear. No private notion replaces the dependency.
3. A nonnegative resolution and augmentation: the integer-indexed cochain
   complex G, `[G.IsStrictlyGE 0]`, the map e from `single ... 0` applied
   to F, and `[QuasiIso e]`. This is a quasi-isomorphism of the stipulated
   complexes, not an injective resolution assumption. No upper bound is added.
4. Flasque underlying abelian sheaves: hfl uses `toSheaf` on every G.X q
   for natural q. Read the actual `TopCat.Sheaf.IsFlasque` abbreviation and
   presheaf class: all restrictions are epi in AddCommGrpCat, equivalently
   surjective. Negative terms are zero, so no flasqueness case is missing.
5. Finite ordered cover: `r : ℕ`, `V : Fin r → X.Opens`, `iSup V = ⊤`.
   Fin r has exactly the node's order, with no positivity assumption.
6. All nonempty subsets S and their intersections: hsections quantifies over
   every p and `t : Fin (p+1) ↪o Fin r`; each subset has a unique increasing
   enumeration. `alternatingCechIntersection V t` is the infimum of its opens.
   This is neither all tuples with repetitions nor only singleton intersections.
7. Section augmentation quasi-isomorphisms: hsections maps e by the composite
   forget/evaluation functor. Read Mathlib's evaluation definition: it is
   exactly this composite. Applied to F[0], it is the single complex of
   sections, and its target is the section complex of G. The local scalar
   ring differs from the global scalar ring only by restriction of scalars;
   the quasi-isomorphism condition is unchanged.
8. L with alternating restriction differential: `(alternatingCechModuleFunctor V).obj F`.
   Read the dependency's actual tuple product, signed face differential,
   extension to integer degrees and module-presheaf construction. These give
   the stated finite products, signs and zero negative terms.
9. D with commuting differentials and totalization: the same functor applied
   termwise and flipped in `alternatingCechDoubleFunctor`, followed by total.
   Read both functors and Mathlib's integer total signs: first degree is Cech,
   second is resolution, with differential d_h + (-1)^p d_v. Nonnegativity
   comes from extension by zero and G.IsStrictlyGE, with no extra instance input.
10. Alpha: `alternatingCechAugmentationMap V G`. Read its component definition:
    singleton restriction followed by `ιTotal` at (0,n). The first conjunct
    asserts its quasi-isomorphism, precisely as required.
11. Beta: the existential cochain map has every integer component fixed to
    the Cech map of `e.f 0` followed by `ιTotal` at (n,0). This specifies
    the canonical map uniquely and is followed by `QuasiIso β`; it does
    not merely assert existence of some quasi-isomorphism between the objects.
12. Degree-zero agreement: the equation beginning with globalSectionsFunctor.map
    (e.f 0) is exactly the equality of the two augmentations into total degree 0.
13. Naturality: the universal Y,h,F',G',e',u,v clause imposes exactly the
    augmentation square in degree zero; other source degrees of F[0] are zero.
    Beta' is likewise fixed componentwise. The final two equations give the
    beta and alpha squares, respectively. The target is the same construction
    on pushforward sheaves, not an arbitrary replacement complex. Read
    `Scheme.Modules.pushforward`, `pushforward_obj_obj`,
    `pushforward_obj_presheaf_map` and `pushforward_map_app`: its sections
    over V_S are those over h inverse V_S, and its restrictions and maps
    are exactly the inverse-image-cover restrictions and maps. Inverse image
    preserves finite intersections. All equations are thus in global O_X(X)
    modules after restricting scalars, as required for a scheme morphism.
14. Coefficient maps and open restrictions are the identity and open-immersion
    specializations of 13. There is no flatness condition. G' is a nonnegative
    resolution; the clause does not demand that pushforward preserve its
    quasi-isomorphism. Naturality itself requires no flasqueness or local
    section quasi-isomorphisms on Y. Applying the theorem to Y separately
    gives its two quasi-isomorphisms under exactly those hypotheses there.

Source check: Tag 09SZ assumes only a ringed space, module sheaf, cover and
flasqueness; it has no hidden finiteness or affine assumption. Tag 01EQ gives
these actual alpha and beta maps. Tag 01ET explains the acyclic-intersection
comparison. The node explicitly formulates the cochain version using a given
flasque resolution and the section-augmentation hypothesis. The ordered
product and face formula immediately before Tag 01FJ agree with the imported
construction. Tags 01FJ and 01FM identify it with alternating/usual cochains.
No correction to the node or unit is needed.

Dependency review: opened every stmt_deps record, including the added existing
DAG node def-sc-alternating-cech-total-complex, and the proof comparison record.
The added dependency is already a landed definition node, not a new definition
or dependency-module delivery. No new nodes or sibling modules occur. Read the
actual first-quadrant theorem: its hypothesis is on flipped components (rows
of the unflipped bicomplex); the docstring uses it directly for alpha and after
transposition for beta. Its natural-indexed form applies after restricting the
first-quadrant integer complexes to nonnegative degrees. The docstring carries
all six node proof steps, including finite-cover induction, finite-product
cohomology, signed transposition, degree-zero agreement and naturality. The
module defines no data, proves nothing, and has exactly one theorem with sorry.

Edge cases: r=0 is admitted; the cover then forces X empty, sections are zero
by the empty-cover sheaf axiom, and all tuple products are zero. Empty members
and empty nonempty-subset intersections are admitted. For p>=r no increasing
tuple exists. For r=1 the only surviving Cech degree is zero. At degree zero
both augmentations land in (0,0). At negative degrees the source Cech terms
and relevant resolution terms are zero. Zero F and G are allowed; no
characteristic restriction occurs. The single arbitrary universe u is the
scheme/module universe convention, with no small test-object quantification
that could make a hypothesis vacuous. All variables and universes are bound.

Independent searches, with wording different from the first reader:

- msearch leanfinder: "Flabby resolution finite increasing tuples Cech
  totalization comparison canonical chain maps natural pushforward" returned
  eight Dold-Kan Gamma construction/map hits, not this comparison.
- msearch loogle: `"IsFlasque"` returned the class, pushforward instances,
  short-exact-sequence properties and skyscraper results, not this statement.
- msearch leansearch: "Two canonical quasi-isomorphisms from Cech cochains
  and global sections of a flasque resolution to their double complex
  totalization" was unavailable (Internal Server Error); no absence verdict
  is inferred from that service.
- rg across Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  used `flabby`, Cech/flasque in either order, `ordered.*comparison` and the
  exact declaration name. Opened upstream CechFlasque: its theorem states
  positive exactness of the usual all-tuples abelian Cech complex, not these
  two ordered total comparison maps and naturality. Opened project
  OrderedCechModuleComparison: it compares ordered and usual presentations
  by homotopy equivalence and does not state this result. The construction
  in AlternatingCechTotalComplex is correctly reused. No duplicate was found.

Mechanical review: the node lean.statement equals the complete theorem
signature verbatim; all module lines have at most 100 characters. No private
copy, local notation/instance, hidden let binder or hollow definition occurs.
The first compilation invocation used a relative filename outside the sandbox
and failed before compiling; it was corrected to the absolute sandbox filename.

Validation: scompile.py compiled the delivered module cleanly on the server
(3.2 seconds), together with its required RingedSiteModules overlay (1.0 second),
using nice 19, two threads and the 60-second per-file limit. No warnings or
errors were reported.
