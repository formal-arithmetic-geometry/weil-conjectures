## Worker report

The module `Sheaf.AlgebraicGeometry.DivisorTorsorBoundarySigns` states
`AlgebraicGeometry.Etale.divisor_torsor_boundary_signs`, with its sole proof `sorry`.
It supplies real coordinate maps into the existing actual shifted mapping cone,
a predicate expressing representation through its cycles and homology quotient,
and the actual shifted-inclusion localization boundary. Its Prop-valued structure
`DivisorTorsorBoundarySigns e` packages the clauses of this node; its fields are
assertions, not assumed existence of unspecified canonical maps. No definition
contains postponed data or a proof hole.

The dependency `relative_torsor_cohomology` existentially quantifies a family of
classifiers. Choosing an arbitrary witness would not fix the representatives.
Instead the main theorem quantifies the SAME family `e`, repeats the four exact
compatibility clauses of that dependency, and asserts the present representative
normalization simultaneously. Thus the theorem refines the recorded interface
without choosing data from a nonunique existence statement or defining another
cohomology theory. The representative normalization fixes the relative class,
including the specified trivialization; it is not merely an equality after
forgetting support. No dependency node or original statement is changed.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A scheme T and a closed immersion i:Z→T | `representative` binds `T Z : Scheme.{u}`, `i : Z ⟶ T`, `[IsClosedImmersion i]`. |
| W is the open complement, with its open immersion j | `W : T.Opens`, `(W : Set T) = (Set.range i.base)ᶜ`, and the canonical `W.ι`; `Scheme.Etale.mk W.ι` is its small-site object. |
| An abelian etale sheaf G | `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}` throughout. No geometric finiteness or characteristic assumptions are added. |
| A G-torsor P with specified section s | `Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι)`; the torsor is `P.1` and s is `P.2`. |
| Its canonical relative class | `e T W G I (Quotient.mk _ P)`, where `e` has precisely the zero, ordinary-forgetful, coefficient, and scheme-pullback compatibilities of the recorded classifier. |
| Any nonnegative injective resolution | `I : InjectiveResolution G`; the N-indexed complex is extended by zero using the dependency's `relativeSections`. |
| Signed relative complex and differential D(a,b)=(da,res(a)-db) | The dependency's `relativeSectionComplex` is used directly. `torsorSignedA` is its first cone projection after the shift/extension identifications, and `torsorSignedB` is minus its second projection. In ordinary cone order (a,bOrd), the shifted differential is (da,-dbOrd-res(a)); putting b=-bOrd gives exactly the stated D. |
| Form the canonical torsor extension | `E : Sheaf.Torsor.ExtensionPresentation.{u,u} T P.1` uses its recorded quotient universal property, inclusion, generator, and projection to the constant integer sheaf. This universally quantified model is canonically the same quotient, rather than an arbitrary extension. |
| Any extension h of augmentation | `h : E.middle ⟶ I.cocomplex.X 0` and `E.inclusion ≫ h = I.ι.f 0`. |
| Factor dh through the integer sheaf and evaluate at 1 | The `representative` field asserts existence of the factor `a` with `E.projection ≫ a = h ≫ I.cocomplex.d 0 1`; its global value is `a.hom.app ... (torsorExtensionOne T ...)`. |
| b=h(s) | `h.hom.app (op (Scheme.Etale.mk W.ι)) (E.generator ... P.2)`. |
| The pair represents alpha(P,s) | `TorsorSignedRepresents ... 0 aValue bValue (e ... ⟦P⟧)`: there is a cycle whose two actual coordinates are these values and whose homology quotient is the specified class. This also asserts both cycle equations. |
| Independence of h | The `extensions` field gives x with pair difference `(dx,res x)`. The `representative` field quantifies every extension h, so they all represent the same e-class. |
| Independence of resolution | `resolutions` identifies the class under every augmented identity-coefficient comparison `a : I.Hom J (𝟙 G)`. `coefficient_representatives` states the componentwise formula for the induced cone map. |
| Trivial torsor with any g∈G(W) | `trivial` quantifies g without any extension-to-T assumption and uses `⟨Sheaf.Torsor.trivial G,g⟩`. |
| Representative (0,g), inserted in I⁰(W) | The `trivial` field uses `TorsorSignedRepresents ... 0 0 ((I.ι.f 0).hom.app ... g) ...`. |
| alpha_g=-∂⁰_G(g) | `trivial` asserts the explicit negative equality with `torsorLocalizationBoundary ... 0 x`, where `TorsorSectionRepresents` identifies x with augmented g in H⁰(W,G). |
| Localization boundary b↦(0,-b) | `torsorLocalizationBoundary` is homology of the actual shifted cone inclusion, preceded by Mathlib's shift-homology isomorphism. `localization` states the representative formula for each nonnegative degree; the boundary itself and its naturality are defined in every integer degree. Below zero the extended section complex is zero, so there is no additional nonzero representative case. |
| Any short exact coefficient sequence | `coefficients` binds a `ShortComplex` S of abelian etale sheaves and `_hS : S.ShortExact`. |
| Degreewise split injective resolutions | I,J,K resolve the three terms; a,b are the chain maps; hab is their zero composite; ha,hb are the augmentation squares; hs supplies split rows at every n. These are arbitrary supplied horseshoe models, whose existence is the recorded horseshoe theorem. |
| Ordinary and relative connecting maps | The ordinary map is `(hOpen.δ 0 1 rfl)` on the evaluated split resolution sequence over W. The relative map is the recorded `relativeConnecting ... hs 1`, with its actual homology-sequence normalization. The existential hOpen asserts that evaluating these split rows remains short exact. Both maps thus compute precisely the source's resolution model of the canonical connecting maps. |
| Positive double-boundary equality | `coefficients` equates `relativeConnecting ... (e ... ⟨trivial,g⟩)` with `torsorLocalizationBoundary ... 1 (hOpen.δ 0 1 rfl x)`. |
| Any lift r of the augmented cocycle g | The nested universal r and hr express `(b.f 0)(r)=augmentation(g)`. No global lift over T is required. |
| dr∈I₁¹(W) | The existential c has `(a.f 1)(c)=d_J(r)`. This is the precise, type-correct meaning of identifying I₁ with its image. |
| Both sides represented by (0,-dr) | The last two conjuncts of `coefficients` are the two `TorsorSignedRepresents ... 1 0 (-c) ...` assertions, and `TorsorSectionRepresents ... 1 c ...` also identifies the ordinary boundary. |
| Natural under etale restriction | The classifier's scheme-pullback clause is retained. `restriction_representatives` binds `[Etale h]` and applies the recorded global/open section-transfer maps componentwise. `localization_restriction` and `connecting_restriction` give the boundary squares. |
| Natural under morphisms of coefficient sequences | `coefficient_representatives` and `localization_coefficients` give the componentwise and localization squares. `connecting_coefficients` is the relative connecting square for every short-complex morphism, without requiring chosen splittings to be preserved. |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`; the complementary open uses its canonical immersion.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf` with abelian-group coefficients.
- `Sheaf.CategoryTheory.Sites.TorsorWithSection`: `Sheaf.Torsor.WithSection`, `.Classes`, and its quotient setoid.
- `Sheaf.AlgebraicGeometry.RelativeTorsorCohomology`: `relative_torsor_cohomology`, `relativeSectionMap`, `relativeTransfer`, `relativeConnecting`, and their compatibility interfaces. Its full signature and proof docstring were read; the four classifier clauses are repeated verbatim in the new theorem.
- `Sheaf.AlgebraicGeometry.RelativeEtaleCohomology`: `relativeSections`, `relativeSectionRestriction`, `relativeSectionComplex`, and `relativeCohomology`.
- `WeilConjectures.CategoryTheory.Sites.Torsor`: `Sheaf.nonempty_equiv_H_one_torsor`, the canonical `Sheaf.Torsor.classH1`, and `classH1_lifts`.
- `Sheaf.CategoryTheory.Sites.TorsorExtensionPresentation`: `Sheaf.Torsor.ExtensionPresentation` and all its fields.
- `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`: `InjectiveResolution`, its N-indexed `cocomplex`, augmentation `ι`, and `InjectiveResolution.Hom`.
- `WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions`: `InjectiveResolution.exists_horseshoe_resolutions`; current published source was read with `scompile.py --source`.

The stated proof dependencies are imported as proof-only imports, including
`exists_signedFibre_triangulated`, `boundedInjectiveFibreDescent`, the horseshoe,
and Mathlib homology-sequence formula/naturality. I read the published
`WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial` using
`scompile.py --source`: its declaration explicitly covers only clauses (3)-(4)
of that node, not clause (5). This is an existing proof-interface fault to revisit
in stage 3, not a missing object in this statement: the present file uses the
already recorded concrete `globalResolutionSectionTransfer` and
`openResolutionSectionTransfer`, and the representative restriction assertions
state the exact required formulas. No proof dependency is silently treated as
having an unstated clause.

Edge cases checked before and during writing: W empty; W=T (Z empty); G=0;
identity and zero coefficient maps; split coefficient sequences; g=0; a section
g extending globally; two choices of h; two choices of r; different injective
resolutions and any augmented comparison; arbitrary etale restriction. For
W=T the relative cone is acyclic, and a global g gives D(g). For the zero
coefficient sheaf the classes vanish. A lift r changed by inclusion(t) changes
c by dt and the signed pair by D(0,t). There is no assumption that r, g or the
torsor has a section on T. No disputed statement or source correction was needed.

Searches for existing statements and notions:

- `msearch.py ... leanfinder 'relative torsor class injective extension representative localization boundary signs'`: eight unrelated complex-shape boundary hits, no torsor representative/sign theorem.
- `msearch.py ... loogle 'CategoryTheory.Sheaf.H, CategoryTheory.ShortComplex.ShortExact'`: nine hits including `Sheaf.H.δ` and exactness statements, none computing relative torsor representatives or the two signs.
- `msearch.py ... leansearch 'Relative torsor class and signed cone localization coefficient connecting map'`: eight localization algebra hits, no match.
- `msearch.py ... grep 'relative.*[Tt]orsor|torsor.*[Bb]oundary|signed.*[Ff]ibre' CategoryTheory`: zero Mathlib hits.
- `rg -n 'torsor.*[Bb]oundary|relative.*torsor|lem-pur-divisor-torsor-boundary-signs' /home/ubuntu/weil-src-slopmaster2/WeilConjectures lean/Sheaf/AlgebraicGeometry lean/Sheaf/CategoryTheory/Sites`: upstream had no match; side hits were the relative classifier, supported Kummer specifications, and a Zariski ordinary H¹ boundary theorem. Their source was read. None states this relative representative/sign theorem. The existing PurityRelativeCone boundary is a shifted cone inclusion on general site objects and comes with additional support/pro-etale comparison machinery; the present owning-node helper is its explicit etale specialization using this node's own relativeSectionRestriction, not a second relative cohomology construction.
- `rg` in `dag/lean_names_upstream.json` for this node and the new declaration names found no collision.

Validation: `scompile.py NM lem-pur-divisor-torsor-boundary-signs <module>`
compiled the final module both in the sandbox and at its library path, with no
errors or warnings (5.8 seconds and 6.2 seconds respectively). Only the main
theorem is postponed, with all eight DAG proof steps in its docstring.

## Second reading by NM

The dispatcher explicitly assigned one worker, prohibited starting agents, and
specified independent review by the maintainer. No independent group reader is
claimed here. I reopened the complete node and final file for a second self-check:
the table above matches every hypothesis and clause. I checked particularly that
the second cone coordinate has a minus sign, the augmentation is inserted before
evaluating g, h is allowed to vary, the factor through the integer sheaf is
asserted rather than assumed, and dr is represented by its preimage c under the
first horseshoe inclusion. Both double-boundary representatives are (0,-c).
The classifier is not arbitrarily chosen from the dependency's existence theorem.
The naturality fields do not ask for preservation of degreewise splittings.
The first compilation exposed two long lines; these were shortened, and the
completed final file compiles without warnings. Independent mathematical review
remains with the maintainer as the dispatch brief specifies.
