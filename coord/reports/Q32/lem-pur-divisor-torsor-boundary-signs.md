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

Q32 validation: the exact module and node declaration are already present on
`newtargets-dag` from the reviewed NM delivery. I copied them without changes
and rechecked the declaration and all dependency records before this delivery.
The required searches run for this check were: `msearch.py ... grep
'divisor_torsor_boundary_signs|TorsorSignedRepresents' WeilConjectures` (0
hits), `msearch.py ... loogle
'AlgebraicGeometry.Etale.divisor_torsor_boundary_signs,
AlgebraicGeometry.Etale.TorsorSignedRepresents'` (unknown identifier, no
match), and `msearch.py ... leanfinder 'relative torsor representatives
signed localization boundary'` (8 generic Mathlib hits, no matching
project declaration). The project declaration is therefore the recorded
source of the statement.

## Second reading by Q32

Independent maintainer second reading of immutable delivery
971e3e17bdae495fa17daa736d5593a07f49c6ef. I did not author or previously review it.
The mathematical statement is correct. The following correspondence was checked
against the snapshot, the source text, and the exact dependency declarations.

| Hypothesis or conclusion | Checked rendering and verdict |
| --- | --- |
| T a scheme; i:Z→T closed; W its complementary open | `representative` binds `T Z : Scheme.{u}`, `[IsClosedImmersion i]`, `W : T.Opens`, and equality with the complement of `Set.range i.base`; W.ι is the canonical open immersion. Exact. |
| Abelian étale sheaf and torsor with a specified section | `Sheaf T.smallEtaleTopology AddCommGrpCat.{u+1}` and recorded `Sheaf.Torsor.WithSection`; P.1 is the torsor, P.2 its section. Exact. |
| Canonical relative class and signed resolution model | The same family e as in `relative_torsor_cohomology` is existentially quantified together with its four compatibility clauses and this node's normalization. This asserts a compatible normalized classifier, without choosing an arbitrary witness. `relativeSectionComplex` is the recorded actual mapping cone shifted by -1. Exact. |
| Canonical extension; any resolution and any augmentation extension h | `ExtensionPresentation.{u,u}` has the quotient universal property, natural equivariant generator, and projection sending generators to one. Every such model is canonical up to its unique compatible isomorphism. `InjectiveResolution G` is nonnegative and h is universally quantified with its augmentation equation. No short-exactness assumption on the presentation was added. |
| Factor dh and evaluate at one; b=h(s); representation | `representative` asserts existence of the sheaf morphism a with `E.projection ≫ a = h ≫ d`; its evaluation at `torsorExtensionOne` and the evaluation of h on the generator of P.2 are the actual signed cycle coordinates. `TorsorSignedRepresents` uses iCycles and homologyπ, so includes both cycle equations and the required homology class. Exact. |
| Independence of h and resolution | `extensions` gives the pair difference `(dx,res x)` for all h,h'; `resolutions` treats every identity-augmentation resolution comparison. All h represent the same e-class, and the componentwise comparison formula is explicit. Exact. |
| Trivial torsor with any g; representative and first minus sign | `trivial` inserts g through I.ι in degree zero, represents the class by `(0,g)`, and equates it to minus the actual localization boundary. The auxiliary x is pinned down by the ordinary section representative predicate, not an arbitrary class. Exact. |
| Localization boundary in all degrees | `torsorLocalizationBoundary` is shifted mappingCone.inr on homology, preceded by the inverse shift-homology isomorphism. The latter has no sign on its middle term. `localization` computes `(0,-b)` for every q≥0; negative-degree ordinary section cohomology is zero. Exact. |
| Arbitrary short exact coefficient sequence and split resolution models | `coefficients` binds S.ShortExact, arbitrary I,J,K, chain maps, both augmentation equations, zero composite, and split rows. These are model data whose existence is the recorded horseshoe theorem, not extra restrictions on the coefficient sequence. Evaluated split rows give hOpen.ShortExact and its actual homology-sequence δ. Exact. |
| Positive double-boundary equality and both representatives | For every lift r of augmented g, the existential c satisfies a¹(c)=d(r). The ordinary boundary is represented by c; the relative boundary and localization boundary are each represented by `(0,-c)` and are equated. This is precisely dr viewed in the first subcomplex. Exact. |
| Naturality under étale restriction and coefficient-sequence morphisms | The classifier retains its original scheme/coefficient naturality. The six representative/localization/connecting fields use the recorded relativeSectionMap, relativeTransfer and actual relativeConnecting. All complex morphisms are allowed; splittings need not be preserved. Exact. |

I read all eleven snapshot statement-dependency records. Exact interfaces checked:
Mathlib Scheme, IsClosedImmersion, IsOpenImmersion, smallEtaleTopology and Sheaf;
Injective and InjectiveResolution; side TorsorWithSection, RelativeEtaleCohomology,
RelativeTorsorCohomology and TorsorExtensionPresentation; upstream Torsor.classH1,
classH1_lifts and nonempty_equiv_H_one_torsor. The horseshoe module is absent from
the local clones; its complete published declaration and docstring were read via
`scompile.py --source WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions`.
It provides precisely the split augmented nonnegative resolution sequence needed.
The canonical section-comparison structure and concrete section-transfer maps were
also read, including their cocycle normalization. The four e-compatibilities match
the dependency; the extra normalization is asserted simultaneously, not assumed.

Source checks: Stacks sites-cohomology.tex, lemma-torsors-h1 (03AJ), lines 290-373:
the canonical pushout extension, boundary of one, and solution-torsor inverse;
derived.tex, lemma-injective-resolution-ses (013T), lines 6570 onward;
cohomology.tex, lemma-triangle-sections-with-support (0G71), lines 8625 onward,
and remark-support-functorial (0G78), lines 8850 onward; blueprint main-20261015,
sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md, clause (a).
The relative refinement is a direct calculation, not falsely attributed verbatim
to 03AJ. Mathlib MappingCone.d_fst_v/d_snd_v, Shift.shiftFunctorObjXIso and
ShiftSequence.shiftShortComplexFunctor'/shiftIso were inspected: ordinary cone
coordinates are `(a,bOrd)` with differential `(-da,res a+dbOrd)`; shifting and
putting b=-bOrd yields `(da,res a-db)`. Inclusion gives `(0,-b)`.
For the coefficient lift, D(0,r)=(0,-dr), so the second equality has a positive
sign. Translation by x changes representatives by D(x); changing the lift by
inclusion(t) changes `(0,-c)` by D(0,t).

Edge cases: empty T; W empty; W=T and Z empty; zero G; zero g; globally extending
g; split sequences; identity and zero coefficient morphisms; all choices of h,r
and resolution comparisons. No section of P or lift of g on T is assumed.
For W=T the cone is acyclic; globally extending g gives D(g); for W empty the
relative complex is the absolute complex. Degrees 0 and 1 and the extension by
zero below degree zero have the stated signs. Universes are bound explicitly
with autoImplicit false; u+1 coefficients follow the recorded small-site size
convention and ULift integers, without identifying site object and morphism
universes or adding a finiteness/characteristic hypothesis.

Independent searches used different wording (`relative.*torsor`,
`torsor.*boundary`, `signed.*represent`, `localizationBoundary`) across Mathlib
sites, upstream WeilConjectures and side Sheaf. Existing ordinary/Zariski torsor
boundary representatives and supported Kummer interfaces do not state this
relative two-sign theorem. PurityRelativeCone.boundary is a general shifted cone
inclusion; this helper applies that standard construction to the already recorded
étale restriction complex and its homology, without defining another theory or
using its pro-étale comparison. All nine local declarations are listed in lean.
No hollow data or arbitrary chosen maps are present. All declaration/module
source and blueprint docstrings and the eight-step theorem proof were read.
The node's lean.statement matches the file's signature verbatim after folding
layout whitespace, and is unchanged by this repair. No statement_change or
citer audit is necessary because no mathematical statement is changed.

Findings repaired mechanically under the landing instruction:
- H6: inline `by omega`, `by simp` and `by rfl` in coordinate transport proofs.
  Replace with existing add/neg cancellation, Nat.cast_add, equality composition,
  and rfl proof terms. No new theorem, axiom, or postponed helper is introduced.
- H11: the delivered Q32 second-reading section was only a disclaimer. Replace
  it with this actual independent reading; retain the full Worker report and
  historical NM section. No worker independence is fabricated.

The previously reported omission of clause 5 from the published pullback-
functorial theorem is a proof-interface observation, not a missing notion or
an assumption of this theorem: its restriction assertions are themselves stated
using concrete transfers, and the relative-classifier interface already supplies
scheme naturality. It is not used as evidence that the missing clause is proved.
There is no missing statement prerequisite needed to type the delivery and no
reason to demand BLOCKED. The proof-only import remains a stage-3 citation concern.

Route pivot: compared all direct statement/proof dependency ids with the current
origin/newtargets-dag coord/route-pivot-dropped.txt: empty intersection. No repair
note exists at coord/repair-notes/lem-pur-divisor-torsor-boundary-signs.json on that
ref. The delivery uses ordinary complexes, injective resolutions and homotopy/
derived categories; no enhanced, dg, model-category or pro-étale replacement.

Compiler evidence and final checks (2026-10-18):

- Original immutable module: `python3 /home/ubuntu/weil-launcher-nt/scompile.py
  Q32 lem-pur-divisor-torsor-boundary-signs
  snapshot/lean/Sheaf/AlgebraicGeometry/DivisorTorsorBoundarySigns.lean` exited 0.
  Sandbox check reported 13.2 s; library-path check 7.0 s; no diagnostics.
- Complete corrected module: the same command with
  `fixes/lean/Sheaf/AlgebraicGeometry/DivisorTorsorBoundarySigns.lean` exited 0.
  Sandbox check reported 16.1 s; library-path check 108.4 s; no diagnostics.
  The wrapper announces a 60 s Lean limit after slot acquisition; its reported
  overall library duration includes wrapper work/waiting. No timeout setting
  was changed. This is evidence of wrapper success, not a claim of a 108 s
  unrestricted Lean invocation.
- The installed scompile.py is the 2026-10-17 server-overlay wrapper, despite
  the older brief's local-wrapper description. It checks imports in a private
  overlay and confirms the library-path check. I used the prescribed wrapper;
  no direct ssh, lake build, global build, or live Lean edit was run.
- Original module SHA256:
  0710be6c54331cfc942b2fc55bc98bf3e508dbbf9d304f246a26cb04115bc07d.
  Corrected module SHA256:
  ac9827332d8f4fb84a3ec37c652b95c061f52345905b74a3effb240e670beddb.
- Final static checks: all nine declarations recorded; autoImplicit false;
  no line over 100 characters; exactly one sorry, in the named main theorem;
  no inline tactic blocks except that theorem's `by sorry`; unchanged normalized
  signature exactly equals lean.statement; complete source/blueprint docstrings.
  Worker report retained and Q32 second reading replaced with a real reading.
  No mathematical statement or dependency record changed, so no §1(C) audit.
- FIX contains complete replacements at
  `fixes/lean/Sheaf/AlgebraicGeometry/DivisorTorsorBoundarySigns.lean` and
  `fixes/lem-pur-divisor-torsor-boundary-signs.report.md`. These are respectively
  a delivered library path and the `<item>.report.md` override accepted by
  tools/merge_delivery.py --stage 2. No merge/preflight/delivery was invoked.
- Read-only sources and immutable snapshot were not edited; no Git mutation
  was performed and the delivery branch head was not changed. Writes were
  confined to review.md and fixes/. No remaining substantive finding.
