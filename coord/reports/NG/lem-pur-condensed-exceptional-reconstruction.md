# Stage-1 repair report

Item: lem-pur-condensed-exceptional-reconstruction. Group NG, 2026-10-16. This supersedes the returned report; its original version is retained in the sandbox under returned-version/. Only stage 1. No Lean was authored or compiled, no Lake/build tool ran, no target or parent was edited, and no delivery was pushed.

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-condensed-exceptional-reconstruction.json — split, nine proof steps, no Mathlib match.
- dag/nodes/sec-smooth-purity/lem-pur-finite-coefficient-adjoint-comparisons.json — statement-only, unsplit, no Mathlib match; retained substantive arbitrary-field finite geometric input.
- dag/nodes/sec-smooth-purity/lem-pur-compact-support-condensed-realization.json — statement-only, unsplit, no Mathlib match; retained substantive left-functor realization input.
- citations.json — all 35 step/node occurrences, quoted verbatim from the actual current statements. report.md — this report, with full source exhibits. Source copies, manifest, scripts, and returned-version/ are sandbox reference files only; copied source blobs have .txt suffixes, not authored Lean files.

## Attachments

None. Repeated the done-tree search for the item tag and exceptional/condensed notions and read AlgebraicGeometry.Etale.boundedConstructibleIntegral_exceptionalAdjoint at SixFunctors/Etale/Derived/IntegralCoefficients.lean:321. Its proof contains sorry, its coefficients are ordinary etale, and it does not state the condensed comparison. Neither Mathlib nor the sorried master framework is a project attachment.

## WANTED

None for the comparison definitions or the sources used here. The absent local exact-master paths have been resolved by independently retrieving their exact blobs over read-only ssh from /home/ubuntu/sidebuild-base/repo.git at commit 7347520d9b0d17cc31d0fc34ea20f1381a83fe13. All eleven complete blobs are included below, so this delivery does not depend on installation of the literature mirror. No source theorem of Bhatt–Scholze or SGA is assigned an invented Stacks tag.

## Returned points and their repairs

1. **F1/C4: exact source unavailable.** The retained excerpts were from /home/ubuntu/weil-newtargets-master, a different checkout: its functors take explicit k and schemes with Over instances, while the required revision uses objects and arrows of Over (Spec k) and an implicit k. I did not assume those interfaces were identical. I read the exact-commit UpperShriek, BoundedConstructible, Basic, constructible sheaf and derived category definitions, continuous/finite-extension-valued coefficient rings, coefficient changes, compactification Over construction, and open derived adjunction. Read-only git show ran only on the server's separate source object store, never in the shared project. Computed Git blob and SHA-256 hashes from every returned byte. All eight overlaps with the accepted parent report match both of its hashes. Basic and the two other newly obtained files now make the coefficient pullback and compactification/open-adjunction definitions independently checkable. Full bytes and hashes are below.

2. **C4/E1: parent did not supply strengthened coherent-system data.** Repaired the statement and proof, rather than leaving a scope note for somebody else. The lemma now allows either an enhanced identification or a strict exceptional-image system concentrated in one common degree r, with the already required commuting level identifications. Its new elementary Step 3 constructs the enhanced comparison in the latter case: for either strict representative C use the natural quasi-isomorphism zigzag C ← tau_le_r C → H^r(C)[-r]; the commuting level identifications become an actual isomorphism of the abelian cohomology diagrams. Conjugating gives a derived-system isomorphism whose evaluations are the specified maps. The counit is transported from the geometric section adjunction. This is not a claimed lifting theorem for arbitrary transformations in derived homotopy categories.

The immutable parent nt-target-smooth-purity-qbar satisfies this alternative from its existing cited statements: lem-pur-finite-smooth-adjunction-general-base explicitly says both sides of gamma_n at the finite unit have cohomology only in degree -2d and explicitly supplies quotient compatibility and cocycle. The parent's Step 1 defines M_bullet as the strict twist-sheaf tower placed in that same degree. Its identifications are gamma_n, its transitions are the quotient/power maps, and their intertwining is the finite lemma's coefficient compatibility. Thus r=-2d works for every n, over every allowed field k, and no enhanced finite-purity theorem or new target hypothesis is needed. Step 2 of the parent already supplies integral membership and the actual normalized reductions. The parent's Step 4 now applies through the proved alternative. No parent text, target signature or target field class changed.

## Statement disputes

STATEMENT-DISPUTED: the imported general formulation gave only a strict tower with homotopy-category transition identifications but asserted a specified derived-system counit. Its general, multiple-degree interpretation leaves higher comparison data unspecified. The previous delivery repaired this by assuming enhanced identification, which the parent did not furnish. The current statement retains that general enhanced case and adds the fully proved common-single-degree case that covers the source's actual finite-unit use. The conclusion, chosen constructible right adjoint, counit, refinement and morphism compatibility, and tensor-unit/shift claims are all retained. The invalid arbitrary-k reference to def-weil-exceptional-inverse-image (which fixes an algebraically closed finite-field base) stays replaced by the written ordinary-etale/site-comparison construction in the finite geometric node. A chosen proper right adjoint is data already required by the exact master definition, not a claim that its sorry instance is a proved attachment.

## Sources and search audit

Read the chapter and purity-transport unit records, their fixed finite-to-adic-to-rational route, SETUP's three levels, GOAL, dag-sync, worker and stage-1 contracts, and delivery-errors B–E. The parent remains split and reviewed; the item remains unsplit in the shared current baseline. The retained split is the returned proposal, not a finished live node. The delivery tool rebases the repaired sandbox fields onto current origin, keeping maintainer metadata.

Read Bhatt–Scholze 6.6.11, 6.7.16–19 and 6.8.14–15 from the obtained PDF text: 6.7.18 gives finite exceptional adjunction and restriction/derived-quotient comparisons; 6.7.19 uses completeness to reconstruct adjunction; 6.8.14 motivates rational realization, while 6.8.15 does not literally prove this exact condensed comparison. Read SGA4 XVIII 3.1.4 and 3.1.12.1 for etale adjunction/restriction of scalars, and 3.2.5 for the parent's finite smooth unit. Read Stacks 0118, homology.tex, section-truncations, for the new explicit elementary truncation argument; Stacks 01T6, morphisms.tex, lemma-finite-type-noetherian, supplies local noetherianity. The enhanced finite-free and simultaneous condensed comparisons remain honestly agent-formulated statement-only obligations, not quotations of a nonexistent source theorem.

Searched the whole DAG/blueprint for exceptional coefficient, compact support realization, heart, coherent systems, single-degree concentration, and the existing/new ids, and read the possible concentration and section-theory matches. Reused def-kun-truncations and the existing semilinear section theorem. The new Step 3 is kernel/cokernel truncation and a strict cohomology-diagram map, so no new node for a two/three-line diagram argument is created. blueprint_refs ancestor still reports null and the same via chain. Both new nodes retain filled blueprint places and same_as=[], and are neither a clause of exceptional reconstruction nor duplicates of the narrower finite-field statements listed below.

All new-node searches in the retained files have actual msearch.py log entries, including LeanFinder, Loogle, source grep, LeanSearch and a second semantic phrasing. In this repair I independently ran and read the two additional LeanFinder searches recorded in their files: finite etale exceptional coefficient mates, and adic/condensed compact support realization. Each returned eight signatures. They concern discrete or solid condensed modules, etale scheme morphisms, or algebraic local cohomology, not either geometric comparison. No result is an exact or one-line Mathlib specialization. There are two new unsplit nodes and zero Mathlib leaves. The actual query text, result names and digest are preserved; no unavailable service is called a no-match and no unrun query is recorded.

## Not duplicates

lem-pur-finite-coefficient-adjoint-comparisons vs lem-coef-finite-exceptional: the existing statement assumes k = algebraic closure of F_q and also gives a Verdier formula; the new statement needs every positive-characteristic ground field and specified enhanced quotient/finite-free coefficient mates, without a Verdier formula.

lem-pur-finite-coefficient-adjoint-comparisons vs lem-coef-finite-free-extension: the existing finite-free comparison fixes the global algebraically closed finite-field datum; the new statement works over arbitrary k and compares the full finite exceptional adjunction and its mixed quotient diagrams.

lem-pur-finite-coefficient-adjoint-comparisons vs lem-coef-finite-adjunction-diagram-realization: the latter assumes the global finite-field geometry and supplies its system realization. The new node is the missing arbitrary-field finite geometric input; the existing generic section-realization and adjoint-mate tools are reused, not duplicated.

lem-pur-finite-coefficient-adjoint-comparisons vs lem-pur-finite-smooth-adjunction-general-base: the latter assumes smooth pure relative dimension and identifies the smooth trace with twist/shift. The new node assumes no smoothness and asserts no purity/twist formula.

lem-pur-finite-coefficient-adjoint-comparisons vs def-weil-exceptional-inverse-image: the latter defines the transported finite functor; it does not prove finite-Tor preservation or the specified coherent quotient/finite-free mate isomorphisms.

lem-pur-compact-support-condensed-realization vs lem-weil-pbc-condensed-e-realization: the existing equivalence compares pullback and direct image and their adjunctions, not the reconstructed compact-support reduction system, open-extension comparison, and Omega compact-support scalar comparison.

lem-pur-compact-support-condensed-realization vs lem-pur-compact-support-integral-coefficient-comparison: the existing statement assumes the global finite-field datum and only compares integral finite-field scalar extensions. The new node works over arbitrary k and includes the exact condensed realization and finite-extension-valued Omega compact support.

lem-pur-compact-support-condensed-realization vs lem-cbc-integral-compact-support-uniform-restriction: the latter gives preservation for Rp_*j_! with completed coefficients. It does not identify the strict finite compact-support tower with reductions, or its J/Omega realization and scalar-extension coherences.

lem-pur-compact-support-condensed-realization vs lem-weil-compact-support-reduction-tower-functor: the existing strict lift supplies an ambient actual tower with its evaluations and transitions; it does not assert its normalized reduction isomorphisms, integral constructible reconstruction, or condensed realization.

lem-pur-compact-support-condensed-realization vs lem-cbc-completed-extension-zero-comparison: this is only open extension and completed open-square exchange. It supplies neither the proper direct-image comparison nor the full compact-support realization.

lem-pur-compact-support-condensed-realization vs lem-pod-compact-support-finite-coefficient-comparison: the latter concerns a cohomological injection for the constant sheaf on a geometric finite-field fibre, not a relative functor or its condensed realization.

lem-pur-compact-support-condensed-realization vs lem-pur-condensed-exceptional-reconstruction: the item identifies a supplied reconstructed exceptional system with a specified right adjoint and its counit. The new node contains no exceptional functor, adjunction or comparison with any right adjoint.

## Review by NG

I read the current statement of every cited node, the item and both retained new nodes, and the cited sources. I checked every hypothesis and clause against B–E, not just quotation membership. The nine steps now mean:

1. **Finite Tor inputs.** pqf-lem-locnoeth-lft, qcqs-over-affine and dimension-finite-type apply to finite-type separated schemes over a field. The stratified-perfect characterization gives bounded finite projective local models, and the fpqc covering condition plus finitely many strata gives one finite Tor interval independent of n. The covering detection, ringed tensor-pullback and open-closed statements really apply to arbitrary test coefficient sheaves, so no unjustified pro-etale geometric-stalk conservativity is used. Ell is invertible. Integral membership supplies the etale-origin witnesses.

2. **Finite geometric section adjunction.** The finite new node supplies the actual invertible coefficient mates, finite-Tor preservation and specified counits over the given arbitrary k. The semilinear theorem supplies enhanced models for the actual open/proper/tensor constructions, and cartesian-section-adjoint-mates supplies G, the section counit and the mapping-system adjunction. These are assertions of those statements; no proof-internal construction or finite-field-only lemma is borrowed.

3. **The repair's coherence construction.** The semilinear node explicitly says exactness is componentwise, hence cohomology is componentwise. def-kun-truncations defines the functorial kernels/cokernels and their maps. With only H^r nonzero, the two displayed arrows are quasi-isomorphisms; applying H^r to each commuting phi square gives a strict diagram isomorphism. Naturality of the truncation zigzags in the individual derived categories identifies its evaluations with phi_n, rather than just some isomorphisms. In the parent application the finite-smooth statement supplies exactly r=-2d and the coefficient squares; I opened that statement and the parent's actual strict-twist construction. No nonexistent higher-purity clause is cited. The elementary label refers to this explicit truncation-and-cohomology calculation, not to the non-elementary adjunction of Step 2.

4. **Completed Hom representation.** The compact-support new node supplies alpha as a map of normalized semilinear systems. The evaluation calculus supplies gamma for any first argument and a normalized second argument, with its actual projection formula; the cartesian-section theorem supplies the mapping-system transpose. Derived completeness of L gives L=L_Y R_Y L. Take H^0 after Rlim. The projection identities identify the reconstructed counit without inferring equality of arbitrary maps from evaluation.

5. **Rational Hom representation.** The rational-category definition gives the raw localized Hom groups, rational-transport applies to the supplied exact linear compact-support functor, and J's equivalence/essential surjectivity gives all condensed E-stage test objects. Tensor inverse R-linear maps with E and conjugate by a. No assertion of full faithfulness after extension to Omega is used.

6. **Finite coefficient extensions.** The completed-scalar node supplies the canonical ordinary/completed finite-free tensor comparison and its completeness. Constructibility together with the stratified-perfect characterization puts the scalar-extended objects in the same integral category. The finite geometric node covers quotients and finite-free maps including mixed coherences and counits. At S/v^m choose en>=m, reduce the comparison at S/t^nS=S/v^(en), and use its quotient mate; cocycles give independence. This yields all F-stage test objects, not just extended E-stage objects. In the single-degree case the initial theta is already a derived-system map, so its coefficient extensions are actual section maps; no further single-degree hypothesis after possibly nonflat reduction is needed.

7. **Omega descent.** The two-colimit statement supplies the explicit morphism colimit over common finite overfields, descent and eventual equality. Apply the compatible Hom bijections and the compact-support projection comparison at each stage. Inverse maps induce inverse colimit maps. The ring is the finite-extension-valued ring defined by the exact master, not all valuation-continuous Omega-valued maps.

8. **The exact chosen right adjoint.** Exact master UpperShriek:100–118/128–146 defines R as proper chosen right adjoint then open pullback, with the composite adjunction. The reconstructed t has transpose c. Bijectivity of postcomposition with c for every C gives an inverse (test C=R(U_YL) for a right inverse and C=U_XM for injectivity). The written transpose formula defines the refinement mate; its transpose is the same finite-counit map by the actual coherences in both geometric new statements. Naturality follows from the already constructed section map and Hom representation, including the single-degree alternative. This is elementary relative to the established bijections and specified adjunctions.

9. **Unit and shifts.** J is derived extension from the completed ring and the flat condensed calculus supplies exact coefficient extension and coherent shift/tensor comparisons. Multiplication B tensor_A A→B and b→b tensor 1 are inverse, hence U sends the integral ring to the actual condensed tensor unit. No purity theorem is used here.

**First new node.** Independently checked its statement against BS 6.7.18 and SGA XVIII 3.1.4/3.1.12.1 and its actual definition dependencies. It introduces k, schemes, compactification, R, positive n, finite coefficient categories, ordinary etale adjoint, site comparison and both mate equations. It assumes no smoothness and no integral or condensed right adjoint. Finite-free and higher coherent clauses are expressly new finite-geometric obligations; they are not falsely attributed to a source's narrower restriction square. Both unit and counit equations have the correct domains. It is strictly smaller than exceptional reconstruction and is statement-only.

**Second new node.** Independently checked BS 6.7.2/6.7.14–17/6.8.14–15, the strict tower theorem, J, the scalar extension definition, and exact master compact-support/condensed definitions. Its alpha and a are genuine non-elementary left-functor comparisons and are left unsplit, not silently inferred from a category equivalence. It introduces the field, middle compactification scheme, coefficient rings, semilinear lift, and ringed open-extension construction. Its condensed composite is exactly j_! then proper Rg_* after inclusion, with no completeness condition imposed on the condensed category. Its projection comparison matches the source's canonical lower-shriek coefficient mate; the master only constructs the comparison in general, while invertibility here is the new obligation. It asserts no right-adjoint comparison. Existing uniform restriction and strict-tower statements supply less, and the older integral-scalar comparison assumes the finite-field datum.

**Small cases and definitions.** Checked f=id, an open immersion, empty schemes, zero complexes, n=1, equal quotient indices, E=F, ramified finite field extensions and torsion objects killed by rationalization. For the new alternative r=0 is ordinary cohomology diagrams; r=-2d is the parent, including d=0. Zero systems satisfy any r and give the zero map through the truncation zigzag. The truncation argument never claims arbitrary multi-degree diagrams are rigid. The base k=F_p(t) is allowed and does not invoke the discarded algebraic-closure-of-finite-field definition. Common finite projective local models, not constructibility alone, justify finite Tor amplitude. All decoded TeX and direct definition dependencies were checked, and both unsplit new nodes have empty proofs/proof_deps/proof_origin.

## What remains

Only the two statement-only finite-geometric and compact-support comparison inputs remain to split in later items. The item's argument is complete conditional on them and the explicitly cited existing DAG statements, with the immutable parent applicability gap now discharged. This is not a claim of closed Lean proofs or of repaired unrelated inherited DAG cycles. Source framework sorries remain visible in the exhibits and are not counted as attachments.

## Exact master source exhibits

These are the complete UTF-8 blobs independently read from the server source object store at commit 7347520d9b0d17cc31d0fc34ea20f1381a83fe13. The shared local October 16 mirror lacks these paths; the full contents are therefore part of this delivered report. The local master checkout is not used as exact-revision evidence. Each Git hash includes the standard blob header; SHA-256 covers the raw file bytes. Existing source sorry bodies are retained verbatim. No compilation or source mutation occurred.

Source `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/UpperShriek.lean`

Git blob: `197c2b7f9a750bfa107231bd4dc190d284a023c1`; SHA-256: `c27c43dce9fe3ca5742e1723242e05667eab9f7496c710376807e29490b9e245`; 197 lines.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!

# The exceptional inverse image on bounded constructible module objects

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. As in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all schemes are
separated and of finite type over `Spec k`, and all morphisms are morphisms of
`Over (Spec (.of k))`.

The exceptional inverse image `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` is constructed on the bounded
constructible derived categories directly, out of the two halves of the derived lower shriek
attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:
```
Rf_!(c) := i_! ⋙ Rg_*,      Rf^!(c) := Rg^! ⋙ i^*,
```
where `i_! ⊣ i^*` is the adjunction along the open immersion `i` on bounded constructible
complexes (`boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction`) and `Rg^!` is a
chosen right adjoint of the bounded constructible pushforward `Rg_*` along the proper `g`. The
adjunction `Rf_!(c) ⊣ Rf^!(c)` is the composite of these two adjunctions.

The only input is that `Rg_* : Dᵇc(Z)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` is a left adjoint for proper `g`. The
constructions take it as an instance argument, and it is assumed (`sorry`) for the `ℓ`-adic
coefficient rings only: the condensed ring `E̲ = C(-, E)` of a finite extension `E` of `ℚ_ℓ`
(`Profinite.continuousMapRingObj E`), the condensed ring `𝒪̲_E = C(-, 𝒪_E)` of its ring of
integers, for `E ⊆ ℚ̄_ℓ` (`Profinite.padicIntegersRingObj ℓ E`), and the condensed ring `ℚ̲̄_ℓ`
(`Profinite.padicAlgClRingObj ℓ`).

Exactly as the lower shriek `boundedConstructibleLowerShriek`, the functor `Rf^!` is `Rf^!(c)`
for the compactification `c = compactificationOverField f` chosen by Nagata's theorem, and the
adjunction `Rf_! ⊣ Rf^!` is the adjunction `Rf_!(c) ⊣ Rf^!(c)`.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleUpperShriekOfCompactification`: `Rf^!(c)` on
  bounded constructible complexes, right adjoint to the lower shriek
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactification` of
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, and
  `ProEtale.CondensedRing.boundedConstructibleUpperShriekOfCompactificationAdjunction`: the
  adjunction `Rf_!(c) ⊣ Rf^!(c)`.
- `ProEtale.CondensedRing.boundedConstructibleUpperShriek`: `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` for
  the chosen compactification, and
  `ProEtale.CondensedRing.boundedConstructibleUpperShriekAdjunction`: the adjunction
  `Rf_! ⊣ Rf^!`.

## Sorried input

- `ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj`:
  for `g` proper, `Rg_*` on bounded constructible `E`-sheaves is a left adjoint.
- `ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj`:
  for `g` proper, `Rg_*` on bounded constructible `𝒪_E`-sheaves is a left adjoint.
- `ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`:
  for `g` proper, `Rg_*` on bounded constructible `ℚ̄_ℓ`-sheaves is a left adjoint.

## Implementation notes

`Rg^!` for proper `g` is `Functor.rightAdjoint`, an arbitrary choice of right adjoint extracted
from the instance, not a construction. Only the adjunction `Adjunction.ofIsLeftAdjoint` should be
used about it.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### The adjunction along a compactification -/

section OfCompactification

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

variable [(boundedConstructibleLowerStar Λ ℓ c.overG).IsLeftAdjoint]

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on bounded constructible complexes: a chosen right adjoint `Rg^!`
of the derived pushforward `Rg_*` along the proper `g`, followed by the pullback `i^*` along the
open immersion `i`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactification :
    Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructibleLowerStar Λ ℓ c.overG).rightAdjoint ⋙
    boundedConstructibleUpperStar Λ ℓ c.overI

/-- The adjunction `Rf_!(c) ⊣ Rf^!(c)` on bounded constructible complexes attached to a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`: the composite of the adjunction `i_! ⊣ i^*`
along the open immersion `i` and of the adjunction `Rg_* ⊣ Rg^!` along the proper `g`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactificationAdjunction :
    boundedConstructibleLowerShriekOfCompactification Λ ℓ c ⊣
      boundedConstructibleUpperShriekOfCompactification Λ ℓ c :=
  (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ c.overI).comp
    (Adjunction.ofIsLeftAdjoint _)

end OfCompactification

/-! ### The adjunction `Rf_! ⊣ Rf^!` -/

section Chosen

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

variable [(boundedConstructibleLowerStar Λ ℓ (compactificationOverField f).overG).IsLeftAdjoint]

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible
complexes: the functor `boundedConstructibleUpperShriekOfCompactification` attached to the chosen
compactification `compactificationOverField f`. -/
noncomputable def boundedConstructibleUpperShriek : Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  boundedConstructibleUpperShriekOfCompactification Λ ℓ (compactificationOverField f)

/-- The adjunction `Rf_! ⊣ Rf^!` on bounded constructible complexes: the adjunction
`Rf_!(c) ⊣ Rf^!(c)` for the chosen compactification `c = compactificationOverField f`. -/
noncomputable def boundedConstructibleUpperShriekAdjunction :
    boundedConstructibleLowerShriek Λ ℓ f ⊣ boundedConstructibleUpperShriek Λ ℓ f :=
  boundedConstructibleUpperShriekOfCompactificationAdjunction Λ ℓ
    (compactificationOverField f)

/-- The derived lower shriek `Rf_!` on bounded constructible complexes is a left adjoint, its
right adjoint being `boundedConstructibleUpperShriek`. -/
instance isLeftAdjoint_boundedConstructibleLowerShriek :
    (boundedConstructibleLowerShriek Λ ℓ f).IsLeftAdjoint :=
  (boundedConstructibleUpperShriekAdjunction Λ ℓ f).isLeftAdjoint

instance isRightAdjoint_boundedConstructibleUpperShriek :
    (boundedConstructibleUpperShriek Λ ℓ f).IsRightAdjoint :=
  (boundedConstructibleUpperShriekAdjunction Λ ℓ f).isRightAdjoint

end Chosen

/-! ### The proper pushforward for the `ℓ`-adic coefficient rings -/

section EllAdic

include k

variable {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]

/-- For a proper morphism `g : Z ⟶ Y` and a finite extension `E` of `ℚ_ℓ`, the derived
pushforward `Rg_* : Dᵇc(Z)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` on bounded constructible `E`-sheaves is a left
adjoint; its right adjoint is the exceptional inverse image `Rg^!` along `g`. -/
instance isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ g).IsLeftAdjoint :=
  sorry

/-- For a proper morphism `g : Z ⟶ Y` and a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the derived
pushforward `Rg_* : Dᵇc(Z)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` on bounded constructible `𝒪_E`-sheaves is a
left adjoint; its right adjoint is the exceptional inverse image `Rg^!` along `g`. -/
instance isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructibleLowerStar (Profinite.padicIntegersRingObj ℓ E) ℓ g).IsLeftAdjoint :=
  sorry

/-- For a proper morphism `g : Z ⟶ Y`, the derived pushforward
`Rg_* : Dᵇc(Z)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` on bounded constructible `ℚ̄_ℓ`-sheaves is a left adjoint;
its right adjoint is the exceptional inverse image `Rg^!` along `g`. -/
instance isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj :
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ g).IsLeftAdjoint :=
  sorry

end EllAdic

end AlgebraicGeometry.ProEtale.CondensedRing
````

Source `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean`

Git blob: `503a487318229b2536a916d6a4e164468e64d1ec`; SHA-256: `dfcc5877cbb6fb4eaba57e32455b682ecc604955b5fa4d1ff951b927f94e7597`; 391 lines.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Compactification.Over
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek

/-!

# The six functors on bounded constructible module objects over `Λ`

Let `Λ` be a commutative condensed ring. For a scheme `X`, the bounded constructible derived
category `D_cons(X_proét, Λ_X)` of module objects over the coefficient ring object
`Λ_X = p_X^* Λ` is the full subcategory
`ProEtale.BoundedConstructible (condensedRingObj Λ X)` of `D(Mod_{Λ_X})`
(`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`), with scoped notation
`Dᵇc(X)⟦Λ⟧`. This file restricts the six functors on `D(Mod_{Λ_X})` of the folder
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived` to these full subcategories.

## The setting

Following Bhatt–Scholze, Section 6.8, in the simplified setting of schemes over a field: fix a
prime `ℓ` and a field `k` of characteristic `p > 0` with `p ≠ ℓ`
(`[Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`). All schemes are separated and of finite
type over `Spec k`: they are objects `X : Over (Spec (.of k))` of the category of schemes over
`Spec k`, with structure morphism `X.hom` locally of finite type, quasi-compact and separated.
All morphisms are morphisms `f : X ⟶ Y` of `Over (Spec (.of k))`, and the functors are those of
the underlying morphism of schemes `f.left`. In the documentation, `X` also stands for the
underlying scheme `X.left`, so that for instance `Dᵇc(X)⟦Λ⟧` is `Dᵇc(X.left)⟦Λ⟧` in the code.
No further hypothesis is imposed on the schemes or morphisms. In particular every such morphism
has a compactification, by Nagata's theorem (`AlgebraicGeometry.HasCompactification.of_over`),
with the choice `compactificationOverField f`. A compactification
`c = (X.left ⟶[i] Z ⟶[p] Y.left)` of `f.left` is a factorization in `Over (Spec (.of k))`,
through the object `c.overObj` and the morphisms `c.overI` and `c.overG` of
`WeilConjectures.Compactification.Over`.

| functor | restriction |
| --- | --- |
| `Lf^* = L((f)^*⟦Λ⟧)` | `boundedConstructibleUpperStar` |
| `Rf_* = R((f)_*⟦Λ⟧)` | `boundedConstructibleLowerStar` |
| `j_! = D((j)_!open⟦Λ⟧)`, `j` an open immersion | `boundedConstructibleOpenImmersionLowerShriek` |
| `- ⊗ᴸ -` | `boundedConstructibleTensor` |
| `RHom(-, -)` | `boundedConstructibleHom` |

The pullback, the pushforward and the extension by zero are the `ObjectProperty.lift` of the
composite of the inclusion with the functor on the ambient derived category, so they are
compatible with the inclusions by construction (`ObjectProperty.liftCompιIso`). The derived
tensor product and the derived hom are instead the monoidal closed structure of the full
subcategory `Dᵇc(X)⟦Λ⟧` (`ObjectProperty.fullMonoidalSubcategory`,
`ObjectProperty.fullMonoidalClosedSubcategory`), given by the instances
`isMonoidal_boundedConstructible` and `isMonoidalClosed_boundedConstructible`; they are again
compatible with the inclusions, the inclusion being strict monoidal (`ObjectProperty.monoidalι`).

The derived lower shriek is not a restriction: it is assembled on bounded constructible
complexes out of the functors above. For a compactification `c = (X ⟶[i] Z ⟶[p] Y)` of `f`,
`Rf_!^c := i_! ⋙ Rp_*` (`boundedConstructibleLowerShriekOfCompactification`), and `Rf_!` is
`Rf_!^c` for the chosen compactification `compactificationOverField f`
(`boundedConstructibleLowerShriek`). Both are compatible with the derived lower shrieks
`Rf_!(c)⟦Λ⟧` and `R(f)_!⟦Λ⟧` on the ambient derived categories
(`boundedConstructibleLowerShriekOfCompactificationCompatibility`,
`boundedConstructibleLowerShriekCompatibility`).

The adjunctions `Lf^* ⊣ Rf_*` and `j_! ⊣ j^*` restrict along the fully faithful inclusions
(`Adjunction.restrictFullyFaithful`), and so does the composition isomorphism
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` (`boundedConstructibleUpperStarComp`). The adjunction
`- ⊗ᴸ - ⊣₂ RHom(-, -)` is the tensor-hom adjunction of the monoidal closed category
`Dᵇc(X)⟦Λ⟧` (`boundedConstructibleTensorHomAdjunction₂`).

The exceptional inverse image `Rf^!` is not the restriction of a functor on the ambient derived
category: it is constructed on bounded constructible complexes directly, for the `ℓ`-adic
coefficient rings `E̲` and `ℚ̲̄_ℓ`, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek`.

## Sorried input

That the six functors preserve bounded constructible complexes is `sorry`ed:
`boundedConstructible_leftDerivedUpperStar_obj`, `boundedConstructible_rightDerivedLowerStar_obj`
and `boundedConstructible_openImmersionLowerShriek_obj`, and the instances
`isMonoidal_boundedConstructible` (`Dᵇc(X)⟦Λ⟧` contains `Λ_X` and is stable under `- ⊗ᴸ -`) and
`isMonoidalClosed_boundedConstructible` (`Dᵇc(X)⟦Λ⟧` is stable under `RHom(-, -)`).

These are theorems for the `ℓ`-adic coefficient rings, the condensed rings `E̲` of a finite
extension `E` of `ℚ_ℓ` and `ℚ̲̄_ℓ` (Deligne's finiteness theorems, Bhatt–Scholze, Section 6.8);
`Λ` is kept general here, the coefficient ring being an input of the statements.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- The bounded constructible derived category `D_cons(X_proét, Λ_X)` of module objects over
`Λ_X = p_X^* Λ`. -/
scoped notation "Dᵇc(" X ")⟦" Λ "⟧" =>
  AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj Λ X)

/-! ### The pullback and the pushforward -/

section UpperLowerStar

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The derived pullback `Lf^*` on module objects over `Λ` preserves bounded constructible
complexes. -/
lemma boundedConstructible_leftDerivedUpperStar_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left)))
    (hK : boundedConstructible (condensedRingObj Λ Y.left) K) :
    boundedConstructible (condensedRingObj Λ X.left) ((L((f.left)^*⟦Λ⟧)).obj K) :=
  sorry

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible complexes: the
restriction of `L((f)^*⟦Λ⟧)`. -/
noncomputable def boundedConstructibleUpperStar : Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((f.left)^*⟦Λ⟧))
    fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f K.obj K.property

/-- The restricted derived pullback is compatible with the inclusions. -/
noncomputable def boundedConstructibleUpperStarCompatibility :
    boundedConstructibleUpperStar Λ ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ L((f.left)^*⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` on bounded constructible complexes:
the restriction of `ProEtale.CondensedRing.leftDerivedUpperStarComp` along the fully
faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (g : Y ⟶ Z) :
    boundedConstructibleUpperStar Λ ℓ (f ≫ g) ≅
      boundedConstructibleUpperStar Λ ℓ g ⋙ boundedConstructibleUpperStar Λ ℓ f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (boundedConstructibleUpperStarCompatibility Λ ℓ (f ≫ g) ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp Λ f.left g.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility Λ ℓ g).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The derived pushforward `Rf_*` on module objects over `Λ` preserves bounded constructible
complexes. -/
lemma boundedConstructible_rightDerivedLowerStar_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hK : boundedConstructible (condensedRingObj Λ X.left) K) :
    boundedConstructible (condensedRingObj Λ Y.left) ((R((f.left)_*⟦Λ⟧)).obj K) :=
  sorry

/-- The derived pushforward `Rf_* : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded constructible complexes:
the restriction of `R((f)_*⟦Λ⟧)`. -/
noncomputable def boundedConstructibleLowerStar : Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(Y.left)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R((f.left)_*⟦Λ⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj Λ ℓ f K.obj K.property

/-- The restricted derived pushforward is compatible with the inclusions. -/
noncomputable def boundedConstructibleLowerStarCompatibility :
    boundedConstructibleLowerStar Λ ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f.left)_*⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes: the restriction of
`ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunction :
    boundedConstructibleUpperStar Λ ℓ f ⊣ boundedConstructibleLowerStar Λ ℓ f :=
  Adjunction.restrictFullyFaithful (derivedUpperStarLowerStarAdjunction Λ f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm
    (boundedConstructibleLowerStarCompatibility Λ ℓ f).symm

end UpperLowerStar

/-! ### The extension by zero along an open immersion -/

section OpenImmersion

include ℓ k

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The extension by zero `j_!` along an open immersion, applied levelwise to complexes of
module objects over `Λ`, preserves bounded constructible complexes. -/
lemma boundedConstructible_openImmersionLowerShriek_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
      (condensedRingObj Λ U.left)))
    (hK : boundedConstructible (condensedRingObj Λ U.left) K) :
    boundedConstructible (condensedRingObj Λ X.left) ((D((j.left)_!open⟦Λ⟧)).obj K) :=
  sorry

/-- The extension by zero `j_! : Dᵇc(U)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` along an open immersion on bounded
constructible complexes: the restriction of the levelwise functor `D((j)_!open⟦Λ⟧)`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriek : Dᵇc(U.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ D((j.left)_!open⟦Λ⟧))
    fun K ↦ boundedConstructible_openImmersionLowerShriek_obj Λ ℓ j K.obj K.property

/-- The restricted extension by zero is compatible with the inclusions. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekCompatibility :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ D((j.left)_!open⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `j_! ⊣ j^*` along an open immersion on bounded constructible complexes: the
restriction of `ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction`
along the fully faithful inclusions, the levelwise `D((j)^*⟦Λ⟧)` being identified with the
derived pullback `L((j)^*⟦Λ⟧)` that `boundedConstructibleUpperStar` restricts. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⊣ boundedConstructibleUpperStar Λ ℓ j :=
  Adjunction.restrictFullyFaithful
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j.left).symm)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).symm
    (boundedConstructibleUpperStarCompatibility Λ ℓ j).symm

end OpenImmersion

/-! ### The derived lower shriek -/

/-- The compactification of the underlying morphism of schemes `f.left` of a morphism `f` of
separated `k`-schemes of finite type chosen by Nagata's theorem
(`AlgebraicGeometry.HasCompactification.of_over`): the compactification
`HasCompactification.compactification f.left` for the instance it provides. It is the
compactification defining `boundedConstructibleLowerShriek`. -/
noncomputable abbrev compactificationOverField {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y) : Compactification f.left :=
  haveI := HasCompactification.of_over f
  HasCompactification.compactification f.left

section Shriek

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_* : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded
constructible complexes attached to a compactification `c = (X.left ⟶[i] Z ⟶[p] Y.left)` of
`f.left`: the extension by zero along the open immersion `i` followed by the derived pushforward
along the proper morphism `p`, both on bounded constructible complexes, for `i` and `p` the
morphisms `c.overI` and `c.overG` of `Over (Spec (.of k))`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactification :
    Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(Y.left)⟦Λ⟧ :=
  boundedConstructibleOpenImmersionLowerShriek Λ ℓ c.overI ⋙
    boundedConstructibleLowerStar Λ ℓ c.overG

/-- `Rf_!^c` on bounded constructible complexes is the restriction of the derived lower shriek
`Rf_!(c)⟦Λ⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationCompatibility :
    boundedConstructibleLowerShriekOfCompactification Λ ℓ c ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ Rf_!(c)⟦Λ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarCompatibility Λ ℓ c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ c.overI) _ ≪≫
    Functor.associator _ _ _

end OfCompactification

variable (f : X ⟶ Y)

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded constructible complexes:
the functor `boundedConstructibleLowerShriekOfCompactification` attached to the compactification
`compactificationOverField f` chosen by Nagata's theorem. -/
noncomputable def boundedConstructibleLowerShriek : Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(Y.left)⟦Λ⟧ :=
  boundedConstructibleLowerShriekOfCompactification Λ ℓ (compactificationOverField f)

lemma boundedConstructibleLowerShriek_eq :
    boundedConstructibleLowerShriek Λ ℓ f =
      boundedConstructibleLowerShriekOfCompactification Λ ℓ (compactificationOverField f) :=
  rfl

/-- The derived lower shriek on bounded constructible complexes is the restriction of the
derived lower shriek `R(f)_!⟦Λ⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekCompatibility :
    haveI := HasCompactification.of_over f
    boundedConstructibleLowerShriek Λ ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f.left)_!⟦Λ⟧ :=
  boundedConstructibleLowerShriekOfCompactificationCompatibility Λ ℓ
    (compactificationOverField f)

end Shriek


/-! ### The derived tensor product and the derived hom -/

section TensorHom

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- The bounded constructible complexes of module objects over `Λ` form a monoidal
subcategory of `D(Mod_{Λ_X})` for the derived tensor product: they contain the unit `Λ_X`
and are stable under `- ⊗ᴸ -`. -/
instance isMonoidal_boundedConstructible :
    (boundedConstructible (condensedRingObj Λ X.left)).IsMonoidal :=
  sorry

/-- The bounded constructible complexes of module objects over `Λ` are stable under the derived
hom `RHom(-, -)`, the internal hom of `D(Mod_{Λ_X})`. -/
instance isMonoidalClosed_boundedConstructible :
    (boundedConstructible (condensedRingObj Λ X.left)).IsMonoidalClosed :=
  sorry

/-- The derived tensor product `- ⊗ᴸ - : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded
constructible complexes: the tensor product of the monoidal structure on the full subcategory
`Dᵇc(X)⟦Λ⟧` (`ObjectProperty.fullMonoidalSubcategory`), the restriction of `-⊗ᴸ-(X)⟦Λ⟧` in
both variables. -/
noncomputable def boundedConstructibleTensor :
    Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  curriedTensor _

/-- The derived hom `RHom(-, -) : Dᵇc(X)⟦Λ⟧ᵒᵖ ⥤ Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible
complexes: the internal hom of the monoidal closed structure on the full subcategory
`Dᵇc(X)⟦Λ⟧` (`ObjectProperty.fullMonoidalClosedSubcategory`), the restriction of `RHom(X)⟦Λ⟧`
in both variables. -/
noncomputable def boundedConstructibleHom :
    (Dᵇc(X.left)⟦Λ⟧)ᵒᵖ ⥤ Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  MonoidalClosed.internalHom

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦Λ⟧`, the restricted functor `K ⊗ᴸ -` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleTensorObjCompatibility (K : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleTensor Λ X).obj K ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (-⊗ᴸ-(X.left)⟦Λ⟧).obj K.obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleTensor, derivedTensor]

/-- For a fixed `K ∈ Dᵇc(X)⟦Λ⟧`, the restricted functor `RHom(K, -)` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleHomObjCompatibility (K : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleHom Λ X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (RHom(X.left)⟦Λ⟧).obj (op K.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

/-- The adjunction with a parameter `- ⊗ᴸ - ⊣₂ RHom(-, -)` on bounded constructible complexes:
the tensor-hom adjunction of the monoidal closed structure on `Dᵇc(X)⟦Λ⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction₂ :
    boundedConstructibleTensor Λ X ⊣₂ boundedConstructibleHom Λ X :=
  MonoidalClosed.internalHomAdjunction₂

/-- For a fixed `K ∈ Dᵇc(X)⟦Λ⟧`, the adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on bounded constructible
complexes: the tensor-hom adjunction `ihom.adjunction K` of the monoidal closed structure on
`Dᵇc(X)⟦Λ⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction (K : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleTensor Λ X).obj K ⊣ (boundedConstructibleHom Λ X).obj (op K) :=
  (boundedConstructibleTensorHomAdjunction₂ Λ).adj K

end TensorHom

end AlgebraicGeometry.ProEtale.CondensedRing
````

Source `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean`

Git blob: `7317ca089711037f20d61f9bee6519878d421a19`; SHA-256: `de7399b9342ff3950b27059b0cb97887d615444dad2820b5ee58d76d0e653643`; 480 lines.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Topology.LocallyConstant.Algebra
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal

/-!

# Condensed coefficient rings and their canonical coefficient morphisms

Let `Λ` be a condensed ring, i.e. a ring object of abelian sheaves on the pro-étale site of a
point `*_proét = (Profinite, coherent topology)`, for instance the condensed rings
`T̲ = C(-, T)` of `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`. Following
Sections 4 and 5 of `WeilConjectures/RefactorInstruction.tex`, this file pulls `Λ` back to every
scheme `X`,
```
Λ_X := p_X^* Λ,
```
along the canonical morphism `p_X : X_proét ⟶ *_proét`, and constructs explicitly the
isomorphisms of ring objects
```
α_f : f^* Λ_Y ≅ Λ_X
```
for every morphism of schemes `f : X ⟶ Y`. These are the coefficient rings and the canonical
coefficient morphisms of the six functors on module objects over `Λ_X`, built in the other files
of `WeilConjectures.SixFunctors.ProEtale.ModuleObject`.

## The profinite test objects

For a profinite set `S`, the ring `LC(S, ℤ)` of locally constant functions `S → ℤ` is the
filtered colimit of the finite products `ℤ^{S_i}` over the finite quotients `S_i` of `S`, so
```
Spec LC(S, ℤ) = lim_i ∐_{S_i} Spec ℤ,
```
the profinite set `S` regarded as a pro-étale scheme over `Spec ℤ`
(`AlgebraicGeometry.ProEtale.profiniteToProEt`). For a scheme `X` with structure morphism
`π_X : X ⟶ Spec ℤ`, the base change
```
X[S] := Spec LC(S, ℤ) ×_{Spec ℤ} X = lim_i ∐_{S_i} X
```
is the pro-étale `X`-scheme of the notes (`AlgebraicGeometry.ProEtale.profiniteToProEtOf`). The
functor `S ↦ X[S]` is the composite of `S ↦ Spec LC(S, ℤ)` with the base change along `π_X`.

## The morphism `p_X` and the comparison `α_f`

Accordingly, the inverse image along `p_X` is the composite
```
p_X^* := π_X^* ∘ p^*,
```
where `p^* : Sheaf *_proét Ab ⥤ Sheaf (Spec ℤ)_proét Ab` is the inverse image along the
continuous functor `S ↦ Spec LC(S, ℤ)` (`AlgebraicGeometry.ProEtale.pointUpperStar`). It is
strong monoidal and braided, so for a commutative condensed ring `Λ` the pullback
`Λ_X = p_X^* Λ` is a commutative ring object of abelian sheaves on `X_proét`
(`AlgebraicGeometry.ProEtale.condensedRingObj`). For `f : X ⟶ Y`, the structure morphisms
satisfy `f ≫ π_Y = π_X`, `Spec ℤ` being terminal, and the comparison
```
f^* p_Y^* = f^* π_Y^* p^* ≅ (f ≫ π_Y)^* p^* = π_X^* p^* = p_X^*
```
is the composition isomorphism `ProEtale.upperStarComp` of the pullbacks, which on the test
objects is the canonical isomorphism `X ×_Y Y[S] ≅ X[S]` of the notes
(`AlgebraicGeometry.ProEtale.upperStarFromPointComp`).

## The canonical coefficient morphisms

* `α_f : f^* Λ_Y ⟶ Λ_X` (`AlgebraicGeometry.ProEtale.condensedPullbackHom`): the component at
  `Λ` of the comparison `f^* ∘ p_Y^* ≅ p_X^*`. It is a morphism of ring objects, and an
  isomorphism for *every* `f`: the coefficients pulled back from the point form a
  Cartesian system. As a morphism of bundled ring objects it is
  `AlgebraicGeometry.ProEtale.coefficientPullbackIso`.
* `η_f : Λ_Y ⟶ f_* Λ_X` (`AlgebraicGeometry.ProEtale.condensedPushforwardHom`): the mate of
  `α_f` under the adjunction `f^* ⊣ f_*`, i.e. the unit `Λ_Y ⟶ f_* f^* Λ_Y` followed by `f_* α_f`.

This file also records the instance `AddCommGrpCat.hasFunctorialFlatResolution`, which the
derived functors on module objects need.

## Main definitions

* `AlgebraicGeometry.ProEtale.profiniteToProEt`: the functor `S ↦ Spec LC(S, ℤ)` from
  profinite sets to the pro-étale site of `Spec ℤ`.
* `AlgebraicGeometry.ProEtale.pointUpperStar`: the inverse image `p^*` from condensed abelian
  groups to abelian sheaves on `(Spec ℤ)_proét`.
* `AlgebraicGeometry.ProEtale.upperStarFromPoint`: the inverse image `p_X^* = π_X^* ∘ p^*`.
* `AlgebraicGeometry.ProEtale.condensedRingObj`: the ring object `Λ_X = p_X^* Λ`, and
  `AlgebraicGeometry.ProEtale.coefficientRing`: the same as a bundled ring object.
* `AlgebraicGeometry.ProEtale.upperStarFromPointComp`: the natural isomorphism
  `f^* ∘ p_Y^* ≅ p_X^*`.
* `AlgebraicGeometry.ProEtale.condensedPullbackHom` and
  `AlgebraicGeometry.ProEtale.condensedPushforwardHom`: the coefficient morphisms `α_f` and `η_f`.

## Main results

* `AlgebraicGeometry.ProEtale.condensedPushforwardHom_id` and
  `AlgebraicGeometry.ProEtale.condensedPushforwardHom_comp`: `η` is compatible with the identity
  and composition isomorphisms of the pushforwards. These are the cases `F = p^* Λ` of the general
  coherences `ProEtale.unitCompUpperStarComp_id` and `ProEtale.unitCompUpperStarComp_comp` of
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence`.

## Sorried input

* `AddCommGrpCat.hasFunctorialFlatResolution`: abelian groups admit functorial flat resolutions,
  by free abelian groups; it is what makes the derived functors with values in `Ab` available.
* `AlgebraicGeometry.ProEtale.weaklyEtale_toSpecZ_profiniteToScheme`: `Spec LC(S, ℤ) ⟶ Spec ℤ`
  is weakly étale, `LC(S, ℤ)` being ind-Zariski over `ℤ` (the filtered colimit of the finite
  products `ℤ^{S_i}`), and ind-Zariski algebras being weakly étale.
* `AlgebraicGeometry.ProEtale.preservesFiniteLimits_profiniteToProEt` and
  `AlgebraicGeometry.ProEtale.coverPreserving_profiniteToProEt`: the functor
  `S ↦ Spec LC(S, ℤ)` preserves finite limits (`LC(-, ℤ)` sends a fibre product of profinite
  sets to the tensor product, and the point to `ℤ`), and sends a finite jointly surjective
  family to a pro-étale covering (the map on underlying spaces of `Spec LC(S, ℤ)` is the
  projection `S × Spec ℤ → S`, so surjectivity is preserved, and the morphisms are weakly
  étale and affine). This is Lemma 4.2 of the notes.
* `AlgebraicGeometry.ProEtale.hasLeftKanExtension_op_profiniteToProEt`: the left Kan
  extensions along the opposite of `S ↦ Spec LC(S, ℤ)` exist, both sites being essentially
  small in `u + 1` and `Ab.{u + 1}` being cocomplete for `u + 1`-small diagrams, exactly as
  for `SmallSite.hasLeftKanExtension_op_overPullback`.
* `AlgebraicGeometry.ProEtale.isIso_η_pointUpperStar` and
  `AlgebraicGeometry.ProEtale.isIso_δ_pointUpperStar`: `p^*` is strong monoidal, being the
  sheafification of a left Kan extension along a finite limit preserving functor, which
  commutes with the objectwise tensor product (as for `ProEtale.isIso_δ_upperStar`).
* `AlgebraicGeometry.ProEtale.isMonoidal_upperStarFromPointComp`: the comparison
  `f^* ∘ p_Y^* ≅ p_X^*` is a monoidal natural isomorphism. It is the mate of the composition
  isomorphism of pushforwards, which is monoidal by `ProEtale.isMonoidal_lowerStarComp`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Functor.LaxMonoidal Functor.OplaxMonoidal

/-- Abelian groups admit functorial flat resolutions, by free abelian groups: the free abelian
group on the underlying set of `M` is flat, and surjects functorially onto `M`. -/
instance AddCommGrpCat.hasFunctorialFlatResolution :
    Abelian.HasFunctorialFlatResolution Ab.{u} :=
  sorry

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### `Spec ℤ` and the structure morphisms -/

/-- The terminal scheme `Spec ℤ`, in the universe `u`. -/
noncomputable abbrev specZ : Scheme.{u} :=
  Spec (.of (ULift.{u} ℤ))

/-- The structure morphism `π_X : X ⟶ Spec ℤ`. -/
noncomputable abbrev toSpecZ (X : Scheme.{u}) : X ⟶ specZ :=
  specULiftZIsTerminal.from X

/-- The structure morphisms are compatible with every morphism of schemes, `Spec ℤ` being
terminal. -/
lemma comp_toSpecZ {X Y : Scheme.{u}} (f : X ⟶ Y) : f ≫ toSpecZ Y = toSpecZ X :=
  specULiftZIsTerminal.hom_ext _ _

/-! ### Profinite sets as pro-étale schemes over `Spec ℤ` -/

/-- The functor `S ↦ LC(S, ℤ)` sending a profinite set to its ring of locally constant
integer-valued functions, contravariantly by precomposition. -/
noncomputable def profiniteToCommRingCatOp : Profinite.{u} ⥤ CommRingCat.{u}ᵒᵖ where
  obj S := op (CommRingCat.of (LocallyConstant S ℤ))
  map f := (CommRingCat.ofHom (LocallyConstant.comapRingHom f.hom.hom)).op

/-- The functor `S ↦ Spec LC(S, ℤ) = lim_i ∐_{S_i} Spec ℤ`, the profinite set `S` regarded as a
scheme. -/
noncomputable def profiniteToScheme : Profinite.{u} ⥤ Scheme.{u} :=
  profiniteToCommRingCatOp ⋙ Scheme.Spec

/-- `Spec LC(S, ℤ) ⟶ Spec ℤ` is weakly étale. See the module docstring. -/
instance weaklyEtale_toSpecZ_profiniteToScheme (S : Profinite.{u}) :
    WeaklyEtale (toSpecZ (profiniteToScheme.obj S)) :=
  sorry

/-- The functor `S ↦ Spec LC(S, ℤ)` from profinite sets to the pro-étale site of `Spec ℤ`. -/
noncomputable def profiniteToProEt : Profinite.{u} ⥤ specZ.{u}.ProEt where
  obj S := ProEt.mk (toSpecZ (profiniteToScheme.obj S))
  map f := MorphismProperty.Over.homMk (profiniteToScheme.map f) (comp_toSpecZ _)
  map_id S := MorphismProperty.Over.Hom.ext (profiniteToScheme.map_id S)
  map_comp f g := MorphismProperty.Over.Hom.ext (profiniteToScheme.map_comp f g)

lemma profiniteToProEt_obj_left (S : Profinite.{u}) :
    (profiniteToProEt.obj S).left = Spec (.of (LocallyConstant S ℤ)) :=
  rfl

/-- The functor `S ↦ Spec LC(S, ℤ)` preserves finite limits. See the module docstring. -/
instance preservesFiniteLimits_profiniteToProEt : PreservesFiniteLimits profiniteToProEt.{u} :=
  sorry

instance : RepresentablyFlat profiniteToProEt.{u} :=
  flat_of_preservesFiniteLimits _

/-- The functor `S ↦ Spec LC(S, ℤ)` sends finite jointly surjective families to pro-étale
coverings. See the module docstring. -/
lemma coverPreserving_profiniteToProEt :
    CoverPreserving (coherentTopology Profinite.{u}) (ProEt.topology specZ) profiniteToProEt :=
  sorry

instance isContinuous_profiniteToProEt :
    profiniteToProEt.IsContinuous (coherentTopology Profinite.{u}) (ProEt.topology specZ) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    coverPreserving_profiniteToProEt

/-- The left Kan extensions along the opposite of `S ↦ Spec LC(S, ℤ)` exist. See the module
docstring. -/
instance hasLeftKanExtension_op_profiniteToProEt (F : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) :
    profiniteToProEt.op.HasLeftKanExtension F :=
  sorry

/-- The profinite test object `X[S] = Spec LC(S, ℤ) ×_{Spec ℤ} X = lim_i ∐_{S_i} X` over a
scheme `X`, as a functor from profinite sets to the pro-étale site of `X`. -/
noncomputable def profiniteToProEtOf (X : Scheme.{u}) : Profinite.{u} ⥤ X.ProEt :=
  profiniteToProEt ⋙
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)

/-! ### The inverse image `p^*` from the point -/

/-- The direct image `p_*` from abelian sheaves on `(Spec ℤ)_proét` to condensed abelian
groups, `(p_* G)(S) = G(Spec LC(S, ℤ))`. -/
noncomputable def pointLowerStar :
    Sheaf (ProEt.topology specZ.{u}) Ab.{u + 1} ⥤
      Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  profiniteToProEt.sheafPushforwardContinuous Ab.{u + 1} (coherentTopology Profinite.{u})
    (ProEt.topology specZ)

/-- The inverse image `p^*` from condensed abelian groups to abelian sheaves on
`(Spec ℤ)_proét`: left Kan extension along `S ↦ Spec LC(S, ℤ)` followed by sheafification. -/
noncomputable def pointUpperStar :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⥤
      Sheaf (ProEt.topology specZ.{u}) Ab.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullback profiniteToProEt Ab.{u + 1}
    (coherentTopology Profinite.{u}) (ProEt.topology specZ)

/-- The adjunction `p^* ⊣ p_*`. -/
noncomputable def pointUpperStarLowerStarAdjunction : pointUpperStar.{u} ⊣ pointLowerStar :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous profiniteToProEt Ab.{u + 1}
    (coherentTopology Profinite.{u}) (ProEt.topology specZ)

/-- The direct image `p_*` is lax monoidal, being the pushforward along a continuous functor. -/
noncomputable instance laxMonoidal_pointLowerStar : pointLowerStar.{u}.LaxMonoidal := by
  unfold pointLowerStar
  infer_instance

/-- The inverse image `p^*` is oplax monoidal, being left adjoint to the lax monoidal `p_*`. -/
noncomputable instance oplaxMonoidal_pointUpperStar : pointUpperStar.{u}.OplaxMonoidal :=
  pointUpperStarLowerStarAdjunction.leftAdjointOplaxMonoidal

/-- The inverse image `p^*` preserves the unit. See the module docstring. -/
instance isIso_η_pointUpperStar : IsIso (η pointUpperStar.{u}) :=
  sorry

/-- The inverse image `p^*` commutes with the tensor product. See the module docstring. -/
instance isIso_δ_pointUpperStar (F G : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    IsIso (δ pointUpperStar F G) :=
  sorry

/-- The inverse image `p^*` is strong monoidal. -/
noncomputable instance monoidal_pointUpperStar : pointUpperStar.{u}.Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal _

/-- The direct image `p_*` is lax braided, being the pushforward along a continuous functor. -/
noncomputable instance laxBraided_pointLowerStar : pointLowerStar.{u}.LaxBraided := by
  unfold pointLowerStar
  infer_instance

/-- The inverse image `p^*` is lax braided (hence braided, being strong monoidal): the
compatibility with the braiding is the mate of the one of `p_*`. In particular `p^*` sends
commutative ring objects to commutative ring objects. -/
noncomputable instance laxBraided_pointUpperStar : pointUpperStar.{u}.LaxBraided where
  braided F G := by
    have h : δ pointUpperStar F G ≫ (β_ (pointUpperStar.obj F) (pointUpperStar.obj G)).hom =
        pointUpperStar.map (β_ F G).hom ≫ δ pointUpperStar G F := by
      change (pointUpperStarLowerStarAdjunction.homEquiv _ _).symm
          ((pointUpperStarLowerStarAdjunction.unit.app F ⊗ₘ
            pointUpperStarLowerStarAdjunction.unit.app G) ≫ μ pointLowerStar _ _) ≫ _ =
        _ ≫ (pointUpperStarLowerStarAdjunction.homEquiv _ _).symm
          ((pointUpperStarLowerStarAdjunction.unit.app G ⊗ₘ
            pointUpperStarLowerStarAdjunction.unit.app F) ≫ μ pointLowerStar _ _)
      rw [← Adjunction.homEquiv_naturality_right_symm]
      erw [← Adjunction.homEquiv_naturality_left_symm]
      rw [Category.assoc, Functor.LaxBraided.braided]
      erw [BraidedCategory.braiding_naturality_assoc]
      rfl
    rw [← cancel_epi (δ pointUpperStar F G), Functor.Monoidal.δ_μ_assoc, reassoc_of% h,
      Functor.Monoidal.δ_μ, Category.comp_id]

/-! ### The inverse image `p_X^*` and the coefficient rings `Λ_X` -/

/-- The inverse image `p_X^* = π_X^* ∘ p^*` from condensed abelian groups to abelian sheaves on
`X_proét`. On the test objects it is the inverse image along `S ↦ X[S]`. -/
noncomputable def upperStarFromPoint (X : Scheme.{u}) :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} :=
  pointUpperStar ⋙ (toSpecZ X)^*[Ab.{u + 1}]

/-- The inverse image `p_X^*` is strong monoidal. -/
noncomputable instance monoidal_upperStarFromPoint (X : Scheme.{u}) :
    (upperStarFromPoint X).Monoidal := by
  unfold upperStarFromPoint
  infer_instance

/-- The inverse image `p_X^*` is lax braided. In particular it sends commutative ring objects to
commutative ring objects. -/
noncomputable instance laxBraided_upperStarFromPoint (X : Scheme.{u}) :
    (upperStarFromPoint X).LaxBraided := by
  unfold upperStarFromPoint
  infer_instance

/-- The coefficient ring `Λ_X = p_X^* Λ` on `X_proét` of a condensed ring `Λ`. -/
noncomputable def coefficientRing (X : Scheme.{u})
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :
    Mon (Sheaf (ProEt.topology X) Ab.{u + 1}) :=
  (upperStarFromPoint X).mapMon.obj Λ

lemma coefficientRing_X (X : Scheme.{u})
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :
    (coefficientRing X Λ).X = (upperStarFromPoint X).obj Λ.X :=
  rfl

/-- The condensed ring `T̲ = C(-, T)` of continuous maps into a topological ring `T`, as a ring
object of condensed abelian groups. -/
noncomputable def continuousMapCondensedRing (T : Type) [TopologicalSpace T] [Ring T]
    [IsTopologicalRing T] : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  Mon.mk (Profinite.continuousMapRingObj T)

/-! ### The comparison `α_f : f^* Λ_Y ≅ Λ_X` -/

section Comparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The natural isomorphism `f^* ∘ p_Y^* ≅ p_X^*`: the composition isomorphism
`f^* ∘ π_Y^* ≅ (f ≫ π_Y)^*` of the pullbacks, followed by `f ≫ π_Y = π_X`. On the test objects
it is the canonical isomorphism `X ×_Y Y[S] ≅ X[S]`. -/
noncomputable def upperStarFromPointComp :
    upperStarFromPoint Y ⋙ (f)^*[Ab.{u + 1}] ≅ upperStarFromPoint X :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft pointUpperStar
    ((upperStarComp Ab.{u + 1} f (toSpecZ Y)).symm ≪≫
      eqToIso (congrArg (upperStar Ab.{u + 1}) (comp_toSpecZ f)))

/-- The comparison `f^* ∘ p_Y^* ≅ p_X^*` is a monoidal natural isomorphism. See the module
docstring. -/
instance isMonoidal_upperStarFromPointComp :
    NatTrans.IsMonoidal (upperStarFromPointComp f).hom :=
  sorry

/-- The comparison `α_f : f^* Λ_Y ≅ Λ_X` of the coefficient rings pulled back from the point,
an isomorphism of ring objects of abelian sheaves on `X_proét`. -/
noncomputable def coefficientPullbackIso
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :
    (f)^*[Ab.{u + 1}].mapMon.obj (coefficientRing Y Λ) ≅ coefficientRing X Λ :=
  (Functor.mapMonCompIso (F := upperStarFromPoint Y) (G := (f)^*[Ab.{u + 1}])).symm.app Λ ≪≫
    (Functor.mapMonNatIso (upperStarFromPointComp f)).app Λ

end Comparison

/-! ### The canonical coefficient morphisms of the six functors on module objects -/

section CoefficientMorphisms

open MonObj

open scoped CategoryTheory.Obj

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]

/-! ### The coefficient ring objects `Λ_X` -/

/-- The coefficient ring object `Λ_X = p_X^* Λ` of abelian sheaves on `X_proét`, with the ring
object structure transported along the strong monoidal functor `p_X^*`. -/
noncomputable abbrev condensedRingObj (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  (upperStarFromPoint X).obj Λ

/-- The coefficient ring object `Λ_X` is commutative when `Λ` is, `p_X^*` being braided. -/
instance isCommMonObj_condensedRingObj [IsCommMonObj Λ] (X : Scheme.{u}) :
    IsCommMonObj (condensedRingObj Λ X) :=
  Functor.isCommMonObj_obj (F := upperStarFromPoint X)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### The canonical coefficient morphisms -/

/-- The canonical coefficient morphism `α_f : f^* Λ_Y ⟶ Λ_X`: the component at `Λ` of the
comparison isomorphism `f^* ∘ p_Y^* ≅ p_X^*`, which on the test objects is the canonical
isomorphism `X ×_Y Y[S] ≅ X[S]`. -/
noncomputable abbrev condensedPullbackHom :
    (f)^*[Ab.{u + 1}].obj (condensedRingObj Λ Y) ⟶ condensedRingObj Λ X :=
  Functor.compAlgHom (upperStarFromPoint Y) (f)^*[Ab.{u + 1}] (upperStarFromPointComp f).hom Λ

/-- `α_f` is a morphism of ring objects. -/
instance isMonHom_condensedPullbackHom : IsMonHom (condensedPullbackHom Λ f) :=
  Functor.isMonHom_compAlgHom _ _ _ _

/-- `α_f` is an isomorphism, for every morphism of schemes `f`. -/
instance isIso_condensedPullbackHom : IsIso (condensedPullbackHom Λ f) :=
  inferInstanceAs (IsIso ((upperStarFromPointComp f).hom.app Λ))

omit [MonObj Λ] in
/-- For an open immersion `j : U ⟶ X`, `α_j : j^* Λ_X ⟶ Λ_U` is an isomorphism. This is the
special case of `ProEtale.isIso_condensedPullbackHom` used by the exceptional operations. -/
lemma isIso_condensedPullbackHom_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (condensedPullbackHom Λ j) :=
  inferInstance

/-- The canonical coefficient morphism `η_f : Λ_Y ⟶ f_* Λ_X`: the mate of `α_f` under the
adjunction `f^* ⊣ f_*`, the unit `Λ_Y ⟶ f_* f^* Λ_Y` followed by `f_* α_f`. -/
noncomputable def condensedPushforwardHom :
    condensedRingObj Λ Y ⟶ (f)_*[Ab.{u + 1}].obj (condensedRingObj Λ X) :=
  (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom (condensedRingObj Λ Y) ≫
    (f)_*[Ab.{u + 1}].map (condensedPullbackHom Λ f)

/-- `η_f` is a morphism of ring objects, for the ring object structure of `f_* Λ_X` induced by
the lax monoidal structure of `f_*`. -/
instance isMonHom_condensedPushforwardHom : IsMonHom (condensedPushforwardHom Λ f) :=
  inferInstanceAs (IsMonHom
    ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom (condensedRingObj Λ Y) ≫
      (f)_*[Ab.{u + 1}].map (condensedPullbackHom Λ f)))

omit [MonObj Λ] in
/-- `η_f` is the mate of `α_f`: it is the unit `Λ_Y ⟶ f_* f^* Λ_Y` followed by `f_* α_f`. -/
@[reassoc]
lemma unitAlgHom_comp_map_condensedPullbackHom :
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom (condensedRingObj Λ Y) ≫
      (f)_*[Ab.{u + 1}].map (condensedPullbackHom Λ f) =
        condensedPushforwardHom Λ f :=
  rfl

omit [MonObj Λ] in
/-- The canonical coefficient morphism `α_f` is the composition isomorphism
`f^* π_Y^* ≅ (f ≫ π_Y)^*` of the pullbacks, followed by `f ≫ π_Y = π_X`, at `p^* Λ`. -/
lemma condensedPullbackHom_eq :
    condensedPullbackHom Λ f =
      (upperStarComp Ab.{u + 1} f (toSpecZ Y)).inv.app (pointUpperStar.obj Λ) ≫
        (eqToHom (congrArg (upperStar Ab.{u + 1}) (comp_toSpecZ f))).app
          (pointUpperStar.obj Λ) := by
  have h₁ : condensedPullbackHom Λ f = (upperStarFromPointComp f).hom.app Λ := rfl
  have h₂ : upperStarFromPointComp f =
      Functor.associator pointUpperStar (toSpecZ Y)^*[Ab.{u + 1}] (f)^*[Ab.{u + 1}] ≪≫
        Functor.isoWhiskerLeft pointUpperStar ((upperStarComp Ab.{u + 1} f (toSpecZ Y)).symm ≪≫
          eqToIso (congrArg (upperStar Ab.{u + 1}) (comp_toSpecZ f))) := by
    unfold upperStarFromPointComp
    rfl
  rw [h₁, h₂]
  exact associator_isoWhiskerLeft_upperStarComp_hom_app Ab.{u + 1} pointUpperStar f _ _
    (comp_toSpecZ f) Λ

omit [MonObj Λ] in
/-- `η` of the identity is the identification `Λ_X ≅ (𝟙 X)_* Λ_X`. -/
lemma condensedPushforwardHom_id (X : Scheme.{u}) :
    condensedPushforwardHom Λ (𝟙 X) =
      (ProEtale.lowerStarId Ab.{u + 1} X).inv.app (condensedRingObj Λ X) := by
  rw [condensedPushforwardHom, condensedPullbackHom_eq]
  exact unitCompUpperStarComp_id Ab.{u + 1} (toSpecZ X) (comp_toSpecZ (𝟙 X))
    (pointUpperStar.obj Λ)

omit [MonObj Λ] in
/-- `η` of a composition is the composition of the `η`'s, up to the composition isomorphism
`g_* ∘ f_* ≅ (f ≫ g)_*`. -/
lemma condensedPushforwardHom_comp {Z : Scheme.{u}} (g : Y ⟶ Z) :
    condensedPushforwardHom Λ (f ≫ g) =
      condensedPushforwardHom Λ g ≫ (g)_*[Ab.{u + 1}].map (condensedPushforwardHom Λ f) ≫
        (ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app (condensedRingObj Λ X) := by
  rw [condensedPushforwardHom, condensedPushforwardHom, condensedPushforwardHom,
    condensedPullbackHom_eq, condensedPullbackHom_eq, condensedPullbackHom_eq]
  exact unitCompUpperStarComp_comp Ab.{u + 1} f g (toSpecZ X) (toSpecZ Y) (toSpecZ Z)
    (comp_toSpecZ f) (comp_toSpecZ g) (comp_toSpecZ (f ≫ g)) (pointUpperStar.obj Λ)

end CoefficientMorphisms

end AlgebraicGeometry.ProEtale
````

Source `WeilConjectures/CategoryTheory/RingObjects/Condensed/EllAdic.lean`

Git blob: `229eca997d6f97a34f68105fbf628baf53a90340`; SHA-256: `9deccecc22e8a6364f8c63505b9bff1ea6ca74b87c235b64c7f18fda1fa1c70e`; 239 lines.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic

/-!

# The condensed coefficient rings `ℤ_ℓ`, `ℚ_ℓ`, `𝒪_E`, `E` and `ℚ̄_ℓ`

Fix a prime `ℓ`. The four *topological* `ℓ`-adic coefficient rings are defined as condensed
rings by their sections on profinite sets, following Section 3 of
`WeilConjectures/RefactorInstruction.tex`:
```
ℤ̲_ℓ(S) := C(S, ℤ_ℓ),   ℚ̲_ℓ(S) := C(S, ℚ_ℓ),   𝒪̲_E(S) := C(S, 𝒪_E),   E̲(S) := C(S, E),
```
with restriction by precomposition and the pointwise ring operations: each is
`Profinite.continuousMapRingSheaf` of the corresponding topological ring. Here `E` is a subfield
of `ℚ̄_ℓ = PadicAlgCl ℓ`, given by an embedding `E → ℚ̄_ℓ`, with the topology restricted from
`ℚ̄_ℓ` (`PadicAlgCl.normedFieldOfAlgebra`), and `𝒪_E = PadicAlgCl.integers ℓ E` is its ring of
integers.

The familiar descriptions `ℤ̲_ℓ ≅ lim_n ℤ/ℓⁿ`, `ℚ̲_ℓ ≅ ℤ̲_ℓ[1/ℓ]`, `𝒪̲_E ≅ lim_n 𝒪_E/ϖⁿ` and
`E̲ ≅ 𝒪̲_E[1/ϖ]` are *not* definitions; they are comparison isomorphisms, to be proved later.

The condensed `ℚ̄_ℓ` is not of the form `C(-, T)`. Following Definition 3.6 of the notes, a
section over a profinite set `S` is a continuous map `S → E` into a finite subextension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, regarded in `ℚ̄_ℓ`: the condensed ring `ℚ̲̄_ℓ` is the subsheaf of
`C(-, ℚ̄_ℓ)` of the maps with values in a finite subextension
(`Profinite.padicAlgClCondensedRing`). The sheaf condition is checked directly: a covering is
refined by a finite jointly surjective family, and finitely many finite subextensions have a
finite compositum. It is *not* `C(-, ℚ̄_ℓ)` for the valuation topology, which has more sections:
a sequence of elements of unbounded degree converging to `0` gives a continuous map on a
convergent sequence that takes values in no finite subextension.

The inclusions `ℤ_ℓ → ℚ_ℓ → E`, `ℤ_ℓ → 𝒪_E → E` are continuous ring homomorphisms, so
postcomposition with them gives morphisms of condensed rings.

## Main definitions

* `Profinite.padicIntCondensedRing`, `Profinite.padicCondensedRing`: the condensed rings
  `ℤ̲_ℓ` and `ℚ̲_ℓ`.
* `Profinite.padicSubfieldCondensedRing`, `Profinite.padicIntegersCondensedRing`: the condensed
  rings `E̲` and `𝒪̲_E`, and `Profinite.padicIntegersRingObj`: the ring object of condensed
  abelian groups underlying `𝒪̲_E`.
* `Profinite.padicIntCondensedRingToPadicCondensedRing`,
  `Profinite.padicCondensedRingToPadicSubfieldCondensedRing`,
  `Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing` and
  `Profinite.padicIntCondensedRingToPadicIntegersCondensedRing`: the inclusions, as morphisms of
  condensed rings.
* `Profinite.padicAlgClCondensedRing`: the condensed ring `ℚ̲̄_ℓ`, and
  `Profinite.padicAlgClRingObj`: the underlying ring object of condensed abelian groups.

-/

@[expose] public section

universe u

open CategoryTheory

namespace Profinite

open AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### `ℤ_ℓ` and `ℚ_ℓ` -/

/-- The condensed ring `ℤ̲_ℓ`, with sections `ℤ̲_ℓ(S) = C(S, ℤ_ℓ)` for the `ℓ`-adic topology. -/
noncomputable abbrev padicIntCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  continuousMapRingSheaf ℤ_[ℓ]

/-- The condensed ring `ℚ̲_ℓ`, with sections `ℚ̲_ℓ(S) = C(S, ℚ_ℓ)` for the `ℓ`-adic topology. -/
noncomputable abbrev padicCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  continuousMapRingSheaf ℚ_[ℓ]

/-- The inclusion `ℤ̲_ℓ ⟶ ℚ̲_ℓ`, a morphism of condensed rings. -/
noncomputable def padicIntCondensedRingToPadicCondensedRing :
    padicIntCondensedRing.{u} ℓ ⟶ padicCondensedRing ℓ :=
  continuousMapRingSheafMap PadicInt.Coe.ringHom continuous_subtype_val

/-! ### Subfields `E` of `ℚ̄_ℓ` -/

section Subfield

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The condensed ring `E̲`, for a subfield `E` of `ℚ̄_ℓ` given by an embedding `E → ℚ̄_ℓ`, with
sections `E̲(S) = C(S, E)` for the topology of `E` restricted from `ℚ̄_ℓ`. -/
noncomputable abbrev padicSubfieldCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheaf E

variable [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]

/-- The inclusion `ℚ̲_ℓ ⟶ E̲`, a morphism of condensed rings. -/
noncomputable def padicCondensedRingToPadicSubfieldCondensedRing :
    padicCondensedRing.{u} ℓ ⟶ padicSubfieldCondensedRing ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap (algebraMap ℚ_[ℓ] E) (continuous_algebraMap_padic_of_algebra ℓ E)

end Subfield

/-! ### The rings of integers `𝒪_E` -/

section Integers

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The condensed ring `𝒪̲_E`, for a subfield `E` of `ℚ̄_ℓ` given by an embedding `E → ℚ̄_ℓ`,
with sections `𝒪̲_E(S) = C(S, 𝒪_E)` into the ring of integers `𝒪_E = PadicAlgCl.integers ℓ E`,
for the topology restricted from `ℚ̄_ℓ`. -/
noncomputable abbrev padicIntegersCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheaf (PadicAlgCl.integers ℓ E)

/-- The inclusion `𝒪̲_E ⟶ E̲`, a morphism of condensed rings. -/
noncomputable def padicIntegersCondensedRingToPadicSubfieldCondensedRing :
    padicIntegersCondensedRing.{u} ℓ E ⟶ padicSubfieldCondensedRing ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap (PadicAlgCl.integers ℓ E).subtype continuous_subtype_val

/-- The condensed ring `𝒪̲_E` as a ring object of condensed abelian groups: the abelian sheaf
underlying `padicIntegersCondensedRing ℓ E`, with the ring object structure
`CategoryTheory.Sheaf.monObj_sheafCompose_obj`. -/
noncomputable abbrev padicIntegersRingObj : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (padicIntegersCondensedRing ℓ E)

/-- The condensed ring `𝒪̲_E` is a commutative ring object of condensed abelian groups. -/
instance isCommMonObj_padicIntegersRingObj : IsCommMonObj (padicIntegersRingObj.{u} ℓ E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  isCommMonObj_continuousMapRingObj (PadicAlgCl.integers ℓ E)

variable [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]

/-- The inclusion `ℤ̲_ℓ ⟶ 𝒪̲_E`, a morphism of condensed rings. -/
noncomputable def padicIntCondensedRingToPadicIntegersCondensedRing :
    padicIntCondensedRing.{u} ℓ ⟶ padicIntegersCondensedRing ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap (padicIntToIntegers ℓ E) (continuous_padicIntToIntegers ℓ E)

end Integers

/-! ### `ℚ̄_ℓ` -/

section PadicAlgCl

/-- The subfunctor of `S ↦ C(S, ℚ̄_ℓ)` on profinite sets of the continuous maps with values in a
finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`: a section is a continuous map into one finite local
field `E`, regarded in `ℚ̄_ℓ`. -/
def padicAlgClSubfunctor :
    Subfunctor (ContinuousMap.yonedaPresheaf Profinite.toTopCat.{u} (PadicAlgCl ℓ)) where
  obj S := {a | a ∈ PadicAlgCl.finiteIntermediateFieldValued ℓ S.unop}
  map {S S'} u a ha := by
    obtain ⟨E, hE, h⟩ := ha
    exact ⟨E, hE, fun x ↦ h _⟩

/-- The sections with values in a finite subextension form a sheaf for the coherent topology:
a covering is refined by a finite jointly surjective family `{Sᵢ ⟶ S}`, and if `a ∘ πᵢ` takes
values in the finite subextension `Eᵢ` for each `i`, then `a` takes values in their compositum,
which is again finite. -/
lemma isSheaf_padicAlgClSubfunctor :
    Presieve.IsSheaf (coherentTopology Profinite.{u}) (padicAlgClSubfunctor.{u} ℓ).toFunctor := by
  rw [Subfunctor.isSheaf_iff _
    (h := (isSheaf_iff_isSheaf_of_type _ _).mp (isSheaf_yonedaPresheaf (PadicAlgCl ℓ)))]
  intro S a ha
  obtain ⟨α, _, Y, π, hπ, hmem⟩ := (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily _).mp ha
  choose E hE h using hmem
  have hsurj : ∀ b : S.unop, ∃ (i : α) (y : Y i), π i y = b :=
    ((Profinite.effectiveEpiFamily_tfae Y π).out 0 2).mp hπ
  refine ⟨⨆ i, E i, inferInstance, fun x ↦ ?_⟩
  obtain ⟨i, y, rfl⟩ := hsurj x
  exact (le_iSup E i) (h i y)

/-- The presheaf of rings `S ↦ {a ∈ C(S, ℚ̄_ℓ) | a takes values in a finite subextension}` on
profinite sets, lifted to `Type (u + 1)`. -/
noncomputable def padicAlgClRingPresheaf : Profinite.{u}ᵒᵖ ⥤ RingCat.{u + 1} where
  obj S := RingCat.of (ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ S.unop))
  map u := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((((ContinuousMap.compRightAlgHom ℤ (PadicAlgCl ℓ) u.unop.hom.hom).toRingHom).comp
          (PadicAlgCl.finiteIntermediateFieldValued ℓ _).subtype).codRestrict
          (PadicAlgCl.finiteIntermediateFieldValued ℓ _) (fun a ↦ by
            obtain ⟨E, hE, h⟩ := a.2
            exact ⟨E, hE, fun x ↦ h _⟩)).comp ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The presheaf of types underlying `padicAlgClRingPresheaf ℓ` is the subfunctor
`padicAlgClSubfunctor ℓ`, lifted by one universe. -/
noncomputable def padicAlgClRingPresheafForgetIso :
    padicAlgClRingPresheaf.{u} ℓ ⋙ forget RingCat.{u + 1} ≅
      (padicAlgClSubfunctor.{u} ℓ).toFunctor ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The presheaf of rings of sections with values in a finite subextension is a sheaf. -/
lemma isSheaf_padicAlgClRingPresheaf :
    Presheaf.IsSheaf (coherentTopology Profinite.{u}) (padicAlgClRingPresheaf ℓ) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget RingCat.{u + 1}),
    Presheaf.isSheaf_of_iso_iff (padicAlgClRingPresheafForgetIso ℓ),
    isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff]
  exact isSheaf_padicAlgClSubfunctor ℓ

/-- The condensed ring `ℚ̲̄_ℓ`, following Definition 3.6 of
`WeilConjectures/RefactorInstruction.tex`: a section over a profinite set `S` is a continuous map
`S → E` into a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, regarded in `ℚ̄_ℓ`, so that two such
maps are identified when they agree pointwise in `ℚ̄_ℓ`. Restriction is precomposition and the
ring operations are computed in a common finite subextension. It is *not* `C(-, ℚ̄_ℓ)` for the
valuation topology of `ℚ̄_ℓ`, which has more sections. -/
noncomputable def padicAlgClCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  ⟨padicAlgClRingPresheaf ℓ, isSheaf_padicAlgClRingPresheaf ℓ⟩

/-- The condensed ring `ℚ̲̄_ℓ` as a ring object of condensed abelian groups: the abelian sheaf
underlying `padicAlgClCondensedRing ℓ`, with the ring object structure
`CategoryTheory.Sheaf.monObj_sheafCompose_obj`. -/
noncomputable abbrev padicAlgClRingObj : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (padicAlgClCondensedRing ℓ)

/-- The condensed ring `ℚ̲̄_ℓ` is a commutative ring object of condensed abelian groups. -/
instance isCommMonObj_padicAlgClRingObj : IsCommMonObj (padicAlgClRingObj.{u} ℓ) :=
  Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (padicAlgClCondensedRing ℓ) fun S
      (a b : ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ S.unop)) ↦ mul_comm a b

end PadicAlgCl

end Profinite
````

Source `WeilConjectures/ConstructibleSheaf/ProEtaleModule/Def.lean`

Git blob: `bb220bbc210709d58f2b1bbe65c0af0188458a6c`; SHA-256: `bebcdb7cadad83ef156e89d88db63fbc0f953243ce8f51139a33a590231af528`; 94 lines.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal

/-!

# Constructible sheaves of modules on the pro-étale site

Let `A` be a closed symmetric monoidal Grothendieck abelian category, `X` a scheme and `R` a
ring object of `Sheaf (Scheme.ProEt.topology X) A`, so that `R`-module objects are the sheaves of
`R`-modules on `X_proét`.

## Local finite presentation

`ProEtale.IsLocallyFinitelyPresented R M`: there is a pro-étale cover `{Uᵢ ⟶ X}` with
`M|_{Uᵢ}` finitely presented, i.e. the cokernel of a morphism
`(R|_{Uᵢ})^{mᵢ} ⟶ (R|_{Uᵢ})^{nᵢ}` of free modules of finite rank. Torsion is allowed.

## Constructibility

This part follows the definitions in **Section 6.8** of
*Bhargav Bhatt and Peter Scholze, The pro-étale topology for schemes*

Constructibility is defined with respect to a finite stratification `X = ∐ₐ Xₐ` by locally
closed subschemes, using the existing notion `Scheme.Stratification` (`ConstructibleSheaf.Defs`);
restriction to a stratum is the pullback along its immersion `Xₐ ⟶ X`. Restriction along a
morphism `g` of schemes (to a stratum, or to a member of a pro-étale cover) uses only that the
pullback `g^*` of pro-étale sheaves is lax monoidal (`ProEtale.monoidal_upperStar`): it
sends `R` to a ring object `g^* R` and `R`-modules to `g^* R`-modules (`Functor.mapMod`).

`ProEtale.IsConstructible R M`: there is a stratification such that for each stratum `Xₐ`,
`M|_{Xₐ}` is pro-étale locally finitely presented over `R|_{Xₐ}`. For `R = 𝒪_{E,X}` these are
the constructible `𝒪_E`-sheaves; for `R = E_X` (with `E` a field) they are the constructible
`E`-sheaves, lisse on the strata.

-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

section Local

variable {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

/-- A sheaf of `R`-modules on `X_proét` is *locally finitely presented* if there is a pro-étale
cover `{Uᵢ ⟶ X}` such that each `M|_{Uᵢ}` is the cokernel of a morphism
`(R|_{Uᵢ})^m ⟶ (R|_{Uᵢ})^n` of free modules of finite rank. -/
def IsLocallyFinitelyPresented (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
    Mod.IsFinitelyPresented ((ProEtale.upperStar A (𝒰.f i)).obj R)
      (((ProEtale.upperStar A (𝒰.f i)).mapMod (R := R)).obj M)

end Local

section Constructible

variable {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

/-- A sheaf of `R`-modules `C` on `X_proét` is *constructible* if there is a finite
stratification `X = ∐ₐ Xₐ` such that for every stratum `Xₐ`, `C|_{Xₐ}` is pro-étale locally
finitely presented over `R|_{Xₐ}`.

For `R = 𝒪_{E,X}` these are the constructible `𝒪_E`-sheaves. For `R = E_X` these are the
constructible `E`-sheaves, i.e. the sheaves whose restrictions to the strata of a
stratification are lisse. -/
def IsConstructible (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R) : Prop :=
  ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
    IsLocallyFinitelyPresented ((ProEtale.upperStar A (S.immersion a)).obj R)
      (((ProEtale.upperStar A (S.immersion a)).mapMod (R := R)).obj M)

end Constructible

end AlgebraicGeometry.ProEtale
````

Source `WeilConjectures/ConstructibleSheaf/ProEtaleModule/DerivedCategory.lean`

Git blob: `4e2c26fd4485057184d30f9e329ebffb2395e1f4`; SHA-256: `167bc109ae722728ba5032d6131529559b1bb1d913655b6a25b91c8231861eb6`; 96 lines.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def

/-!

# Bounded constructible derived categories of sheaves of modules on the pro-étale site

Let `A` be a closed symmetric monoidal Grothendieck abelian category, `X` a scheme, `R` a
commutative ring object of `Sheaf (Scheme.ProEt.topology X) A`. The derived category of
sheaves of `R`-modules is
```
D(X_proét, R) := DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R).
```
The *bounded constructible* derived category `ProEtale.BoundedConstructible R` is the full
subcategory of `D(X_proét, R)` (`ProEtale.boundedConstructible R`) consisting of the complexes
`K` such that

1. `K` is bounded, i.e. `Hⁱ(K) = 0` for `i` outside a finite interval (for the canonical
   t-structure, see `ProEtale.mem_boundedConstructible_iff`);
2. every cohomology sheaf `Hⁱ(K)` is constructible (`ProEtale.IsConstructible R`).

Morphisms are computed in `D(X_proét, R)`. For `R = 𝒪_{E,X}` this is `D_cons(X_proét, 𝒪_E)`;
for `R = E_X` it is `D_cons(X_proét, E)`.
No derived completeness condition is imposed.

## Sorried input

The bounded constructible complexes on a topologically noetherian scheme form a triangulated
subcategory (`ProEtale.isTriangulated_boundedConstructible`). This rests on the fact that
constructible sheaves on such a scheme are closed under kernels, cokernels and extensions,
which is not formalized; the instance is `sorry`ed. Noetherianity is assumed only there: the
definition `ProEtale.boundedConstructible` makes sense on any scheme. The derived category
itself uses the `sorry`ed instances of
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory`.

-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}}
  (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R] [IsCommMonObj R]

/-- The bounded constructible complexes of sheaves of `R`-modules on `X`: the complexes `K`
which are bounded for the canonical t-structure and all of whose cohomology sheaves `Hⁿ(K)`
are constructible. -/
noncomputable def boundedConstructible :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)) :=
  DerivedCategory.TStructure.t.bounded ⊓ fun K ↦ ∀ n : ℤ,
    IsConstructible R ((DerivedCategory.homologyFunctor _ n).obj K)

omit [IsCommMonObj R] in
/-- A complex is bounded constructible iff its cohomology sheaves vanish outside a finite
interval `[a, b]` and are all constructible. -/
lemma mem_boundedConstructible_iff
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)) :
    boundedConstructible R K ↔
      (∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
      ∀ n : ℤ, IsConstructible R ((DerivedCategory.homologyFunctor _ n).obj K) := by
  refine and_congr_left' ⟨?_, ?_⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨a, b, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff K a).1 ha i hi
    · exact (DerivedCategory.isLE_iff K b).1 hb i hi
  · rintro ⟨a, b, h⟩
    exact ⟨⟨a, (DerivedCategory.isGE_iff K a).2 fun i hi ↦ h i (Or.inl hi)⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).2 fun i hi ↦ h i (Or.inr hi)⟩⟩

/-- The bounded constructible derived category `D_cons(X_proét, R)`. -/
abbrev BoundedConstructible : Type _ :=
  (boundedConstructible R).FullSubcategory

/-- The bounded constructible complexes on a topologically noetherian scheme form a triangulated
subcategory. -/
instance isTriangulated_boundedConstructible [TopologicalSpace.NoetherianSpace X] :
    (boundedConstructible R).IsTriangulated :=
  sorry

end AlgebraicGeometry.ProEtale
````

Source `WeilConjectures/SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean`

Git blob: `7fee1fe3d0a1bb70fae3fe4462bdf1fd32c96d32`; SHA-256: `18ba53d27bb8a6aa93ca04a8462110f12637384160c36a6c3bc134d0ed78a05c`; 340 lines.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek

/-!

# Compatibility of the six functors with a change of condensed coefficient rings

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, i.e. of commutative ring objects
of abelian sheaves on `*_proét`. For a scheme `X`, its pullback along `p_X` is a morphism of ring
objects `a_X : Λ_X ⟶ Λ'_X` (`ProEtale.coefficientMap`), inducing the *derived extension of
scalars*
```
T^X = Λ'_X ⊗ᴸ_{Λ_X} - = L(Ext_{a_X}) : D(Mod_{Λ_X}) ⥤ D(Mod_{Λ'_X}).
```
This file constructs the *canonical comparison transformations* between these and the derived
functors `Lf^*`, `Rf_*`, `Rf_!` on module objects of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject`, for a morphism of schemes `f : X ⟶ Y`.
Following Corollary `cor:coeff-functor` of `WeilConjectures/RefactorInstruction.tex`, the
coefficient changes `a_X` are compatible with the canonical coefficient morphisms: the squares
```
  f^* Λ_Y --f^* a_Y--> f^* Λ'_Y              Λ_Y ----a_Y----> Λ'_Y
     |                     |                   |                |
    α_f                   α_f                 η_f              η_f
     ↓                     ↓                   ↓                ↓
    Λ_X -------a_X------> Λ'_X              f_* Λ_X --f_* a_X--> f_* Λ'_X
```
commute (`ProEtale.map_coefficientMap_comp_condensedPullbackHom`,
`ProEtale.condensedPushforwardHom_comp_map_coefficientMap`): the first is the naturality in `Λ`
of the comparison `f^* ∘ p_Y^* ≅ p_X^*`, and the second follows by adjunction. From these
squares, by the mate and conjugate constructions of
`WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`:

* **restriction of scalars commutes with the pushforward**, strictly
  (`ProEtale.CondensedRing.comapLowerStarIso`): both composites are `mapMod(f_*)` followed by
  the restriction of scalars along the common composite of the square; and in the derived
  categories (`ProEtale.CondensedRing.derivedComapLowerStarIso`), when `Λ'_X` is flat over
  `Λ_X`, so that the restriction of scalars preserves K-injective complexes;
* **(Pull)** `Lf^*_Λ ⋙ T^X ≅ T^Y ⋙ Lf^*_Λ'` (`ProEtale.CondensedRing.derivedPullIso`, and the
  underived `ProEtale.CondensedRing.pullIso`): the *conjugates* of the previous isomorphisms
  along `Lf^* ⊣ Rf_*` and `L(Ext) ⊣ D(Res)`, hence isomorphisms on all unbounded objects;
* **(Push)** `Rf_*^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_*^Λ'` (`ProEtale.CondensedRing.derivedPushHom`, and the
  underived `ProEtale.CondensedRing.pushHom`): the *mates* of the previous isomorphisms. They
  are not isomorphisms in general;
* **restriction of scalars commutes with the pullback**
  (`ProEtale.CondensedRing.comapUpperStarIso`), since every `α_f` is an isomorphism, and with
  the extension by zero along an open immersion `j`
  (`ProEtale.CondensedRing.comapOpenImmersionLowerShriekIso`). Hence the comparison
  `j_!^Λ ⋙ T^X ≅ T^U ⋙ j_!^Λ'` is an *isomorphism*, being the conjugate of the former along
  `j_! ⊣ j^*` (`ProEtale.CondensedRing.openImmersionShriekIso`, and its derived version
  `ProEtale.CondensedRing.derivedOpenImmersionShriekIso`);
* **(Shriek)** `Rf_!^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_!^Λ'`
  (`ProEtale.CondensedRing.derivedLowerShriekHom`), for `Rf_! = Di_! ⋙ Rg_*` attached to the
  chosen compactification `X ⟶[i] Z ⟶[g] Y` of `f`: the derived (Push) for the proper `g`
  followed by the derived (Shriek) isomorphism for the open immersion `i`. It is an
  isomorphism whenever (Push) is one for `g`
  (`ProEtale.CondensedRing.isIso_derivedLowerShriekHom`).

The compatibilities with the derived tensor product, the derived hom and `Rf^!` are not
treated: they require the strong monoidality of the extension of scalars, respectively
perfectness or duality hypotheses, which are not formalized.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Abelian

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### The coefficient changes `a_X` and the coefficient morphisms -/

section CoefficientMap

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [MonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

/-- The coefficient change `a_X = p_X^* a : Λ_X ⟶ Λ'_X` on `X_proét` induced by a morphism
`a : Λ ⟶ Λ'` of condensed rings. It is a morphism of ring objects, `p_X^*` being monoidal. -/
noncomputable abbrev coefficientMap (X : Scheme.{u}) :
    condensedRingObj Λ X ⟶ condensedRingObj Λ' X :=
  (upperStarFromPoint X).map a

omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
lemma coefficientMap_id (X : Scheme.{u}) : coefficientMap (𝟙 Λ) X = 𝟙 _ :=
  (upperStarFromPoint X).map_id Λ

omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
lemma coefficientMap_comp {Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    (b : Λ' ⟶ Λ'') (X : Scheme.{u}) :
    coefficientMap (a ≫ b) X = coefficientMap a X ≫ coefficientMap b X :=
  (upperStarFromPoint X).map_comp a b

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
/-- The coefficient morphisms `α_f : f^* Λ_Y ⟶ Λ_X` are natural in the condensed ring:
`f^* a_Y ≫ α_f = α_f ≫ a_X`. This is the naturality in `Λ` of the comparison
`f^* ∘ p_Y^* ≅ p_X^*`. -/
@[reassoc]
lemma map_coefficientMap_comp_condensedPullbackHom :
    (f)^*[Ab.{u + 1}].map (coefficientMap a Y) ≫ condensedPullbackHom Λ' f =
      condensedPullbackHom Λ f ≫ coefficientMap a X :=
  (upperStarFromPointComp f).hom.naturality a

omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
/-- The coefficient morphisms `η_f : Λ_Y ⟶ f_* Λ_X` are natural in the condensed ring:
`η_f ≫ f_* a_X = a_Y ≫ η_f`. This follows from the naturality of `α_f` and of the unit of
`f^* ⊣ f_*`. -/
@[reassoc]
lemma condensedPushforwardHom_comp_map_coefficientMap :
    condensedPushforwardHom Λ f ≫ (f)_*[Ab.{u + 1}].map (coefficientMap a X) =
      coefficientMap a Y ≫ condensedPushforwardHom Λ' f := by
  rw [← unitAlgHom_comp_map_condensedPullbackHom, ← unitAlgHom_comp_map_condensedPullbackHom,
    Category.assoc, ← Functor.map_comp, ← map_coefficientMap_comp_condensedPullbackHom,
    Functor.map_comp]
  exact ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.naturality_assoc _ _).symm

end CoefficientMap

namespace CondensedRing

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-! ### Pushforward and pullback -/

section UpperLowerStar

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Restriction of scalars commutes with the pushforward:
`f_*^Λ' ⋙ Res_{a_Y} ≅ Res_{a_X} ⋙ f_*^Λ`, both being `mapMod(f_*)` followed by the restriction
of scalars along the common composite of the square `a_Y ≫ η_f = η_f ≫ f_* a_X`. -/
noncomputable def comapLowerStarIso :
    (f)_*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a Y) ≅ Mod.comap (coefficientMap a X) ⋙ (f)_*⟦Λ⟧ :=
  Mod.comapMapModComapIso (f)_*[Ab.{u + 1}] (coefficientMap a X) (coefficientMap a Y)
    (condensedPushforwardHom Λ f) (condensedPushforwardHom Λ' f)
    (condensedPushforwardHom_comp_map_coefficientMap a f).symm

/-- **(Pull)**, underived: `f^*_Λ ⋙ Ext_{a_X} ≅ Ext_{a_Y} ⋙ f^*_Λ'`, the conjugate of
`comapLowerStarIso` along `f^* ⊣ f_*` and `Ext ⊣ Res`. -/
noncomputable def pullIso :
    (f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X) ≅
      Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧ :=
  Adjunction.pullIsoOfComapIso (Mod.extendRestrictAdjunction (coefficientMap a X))
    (Mod.extendRestrictAdjunction (coefficientMap a Y))
    (upperStarLowerStarAdjunction Λ f) (upperStarLowerStarAdjunction Λ' f)
    (comapLowerStarIso a f)

/-- **(Push)**, underived: the canonical comparison `f_*^Λ ⋙ Ext_{a_Y} ⟶ Ext_{a_X} ⋙ f_*^Λ'`,
the mate of `comapLowerStarIso` along `Ext ⊣ Res`. -/
noncomputable def pushHom :
    (f)_*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a Y) ⟶
      Mod.extendScalars (coefficientMap a X) ⋙ (f)_*⟦Λ'⟧ :=
  Adjunction.pushHomOfComapIso (Mod.extendRestrictAdjunction (coefficientMap a X))
    (Mod.extendRestrictAdjunction (coefficientMap a Y)) (comapLowerStarIso a f)

/-- For every `f`, restriction of scalars commutes with the pullback:
`f^*_Λ' ⋙ Res_{a_X} ≅ Res_{a_Y} ⋙ f^*_Λ`, since the coefficient morphisms `α_f` are
isomorphisms. -/
noncomputable def comapUpperStarIso :
    (f)^*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a X) ≅ Mod.comap (coefficientMap a Y) ⋙ (f)^*⟦Λ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((f)^*[Ab.{u + 1}].mapMod (R := condensedRingObj Λ' Y))
      (Mod.extendScalarsComapIsoOfIsIso ((f)^*[Ab.{u + 1}].map (coefficientMap a Y))
        (coefficientMap a X) (condensedPullbackHom Λ f) (condensedPullbackHom Λ' f)
        (map_coefficientMap_comp_condensedPullbackHom a f).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((f)^*[Ab.{u + 1}].mapModComapIso (coefficientMap a Y)).symm
      (Mod.extendScalars (condensedPullbackHom Λ f)) ≪≫
    Functor.associator _ _ _

/-- Restriction of scalars commutes with the levelwise derived pullback:
`Df^*_Λ' ⋙ D(Res_{a_X}) ≅ D(Res_{a_Y}) ⋙ Df^*_Λ`. -/
noncomputable def derivedComapUpperStarIso :
    D((f)^*⟦Λ'⟧) ⋙ D(Mod.comap (coefficientMap a X)) ≅
      D(Mod.comap (coefficientMap a Y)) ⋙ D((f)^*⟦Λ⟧) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (comapUpperStarIso a f) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

end UpperLowerStar

/-! ### Derived pushforward and pullback, for a flat coefficient change -/

section Derived

variable [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]

instance preservesHomology_extendScalars_coefficientMap (X : Scheme.{u}) :
    (Mod.extendScalars (coefficientMap a X)).PreservesHomology := {}

/-- The restriction of scalars along a flat coefficient change `a_X : Λ_X ⟶ Λ'_X` preserves
K-injective complexes, its left adjoint being exact. -/
instance preservesKInjectiveComplexes_comap_coefficientMap (X : Scheme.{u}) :
    (Mod.comap (coefficientMap a X) :
      Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X) ⥤
        Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
      ).PreservesKInjectiveComplexes :=
  (Mod.extendRestrictAdjunction (coefficientMap a X)).preservesKInjectiveComplexes

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Restriction of scalars commutes with the derived pushforward:
`Rf_*^Λ' ⋙ D(Res_{a_Y}) ≅ D(Res_{a_X}) ⋙ Rf_*^Λ`. The restriction of scalars is exact and, `Λ'_X`
being flat over `Λ_X`, preserves K-injective complexes, so both sides are the right derived
functor of the two equal composites of `comapLowerStarIso`. -/
noncomputable def derivedComapLowerStarIso :
    R((f)_*⟦Λ'⟧) ⋙ D(Mod.comap (coefficientMap a Y)) ≅
      D(Mod.comap (coefficientMap a X)) ⋙ R((f)_*⟦Λ⟧) :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso (f)_*⟦Λ'⟧
      (Mod.comap (coefficientMap a Y))).symm ≪≫
    Functor.rightDerivedFunctorNatIso (comapLowerStarIso a f) ≪≫
    Functor.rightDerivedFunctorCompIso (Mod.comap (coefficientMap a X)) (f)_*⟦Λ⟧ ≪≫
    Functor.isoWhiskerRight
      (Mod.comap (coefficientMap a X)).rightDerivedFunctorIsoMapDerivedCategory R((f)_*⟦Λ⟧)

/-- **(Pull)**: `Lf^*_Λ ⋙ T^X ≅ T^Y ⋙ Lf^*_Λ'`, the conjugate of `derivedComapLowerStarIso` along
the derived adjunctions. It is an isomorphism on all unbounded objects. -/
noncomputable def derivedPullIso :
    L((f)^*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a X)) ≅
      L(Mod.extendScalars (coefficientMap a Y)) ⋙ L((f)^*⟦Λ'⟧) :=
  Adjunction.pullIsoOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (derivedUpperStarLowerStarAdjunction Λ f) (derivedUpperStarLowerStarAdjunction Λ' f)
    (derivedComapLowerStarIso a f)

/-- **(Push)**: the canonical comparison `Rf_*^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_*^Λ'`, the mate of
`derivedComapLowerStarIso` along `L(Ext) ⊣ D(Res)`. It is not an isomorphism in general. -/
noncomputable def derivedPushHom :
    R((f)_*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a Y)) ⟶
      L(Mod.extendScalars (coefficientMap a X)) ⋙ R((f)_*⟦Λ'⟧) :=
  Adjunction.pushHomOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (derivedComapLowerStarIso a f)

end Derived

/-! ### Extension by zero along an open immersion -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Restriction of scalars commutes with the extension by zero along an open immersion:
`j_!^Λ' ⋙ Res_{a_X} ≅ Res_{a_U} ⋙ j_!^Λ`, by the naturality of the projection formula and the
square of the coefficient morphisms `α_j`. -/
noncomputable def comapOpenImmersionLowerShriekIso :
    (j)_!open⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a X) ≅
      Mod.comap (coefficientMap a U) ⋙ (j)_!open⟦Λ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Mod.comap (condensedPullbackHom Λ' j))
      ((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1}
        j).projectionFormula.mapModLeftComapIso (coefficientMap a X)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Mod.comapComp _ _).symm ≪≫
      Mod.comapIsoOfEq (map_coefficientMap_comp_condensedPullbackHom a j) ≪≫
      Mod.comapComp _ _) _ ≪≫
    Functor.associator _ _ _

/-- **(Shriek) for an open immersion**, underived: `j_!^Λ ⋙ Ext_{a_X} ≅ Ext_{a_U} ⋙ j_!^Λ'`, the
conjugate of `comapUpperStarIso` along `j_! ⊣ j^*` and `Ext ⊣ Res`. -/
noncomputable def openImmersionShriekIso :
    (j)_!open⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X) ≅
      Mod.extendScalars (coefficientMap a U) ⋙ (j)_!open⟦Λ'⟧ :=
  (conjugateIsoEquiv ((Mod.extendRestrictAdjunction (coefficientMap a U)).comp
    (openImmersionLowerShriekUpperStarAdjunction Λ' j))
    ((openImmersionLowerShriekUpperStarAdjunction Λ j).comp
      (Mod.extendRestrictAdjunction (coefficientMap a X)))).symm
    (comapUpperStarIso a j)

/-- **(Shriek) for an open immersion**: `Dj_!^Λ ⋙ T^X ≅ T^U ⋙ Dj_!^Λ'`, the conjugate of
`derivedComapUpperStarIso` along the derived adjunctions `Dj_! ⊣ Dj^*` and
`L(Ext) ⊣ D(Res)`. It is an isomorphism on all unbounded objects. -/
noncomputable def derivedOpenImmersionShriekIso :
    D((j)_!open⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a X)) ≅
      L(Mod.extendScalars (coefficientMap a U)) ⋙ D((j)_!open⟦Λ'⟧) :=
  (conjugateIsoEquiv
    ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U)).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j))
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)))).symm
    (derivedComapUpperStarIso a j)

end OpenImmersion

/-! ### Derived lower shriek -/

section LowerShriek

variable [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- **(Shriek)**: the canonical comparison `Rf_!^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_!^Λ'` for
`Rf_! = Di_! ⋙ Rg_*` attached to the chosen compactification `X ⟶[i] Z ⟶[g] Y` of `f`: the
derived (Push) comparison for the proper `g` followed by the derived (Shriek) isomorphism for
the open immersion `i`. -/
noncomputable def derivedLowerShriekHom :
    R(f)_!⟦Λ⟧ ⋙ L(Mod.extendScalars (coefficientMap a Y)) ⟶
      L(Mod.extendScalars (coefficientMap a X)) ⋙ R(f)_!⟦Λ'⟧ :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D(((HasCompactification.compactification f).i)_!open⟦Λ⟧)
      (derivedPushHom a (HasCompactification.compactification f).g) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (derivedOpenImmersionShriekIso a (HasCompactification.compactification f).i).hom
      R(((HasCompactification.compactification f).g)_*⟦Λ'⟧) ≫
    (Functor.associator _ _ _).hom

/-- **(Shriek)** is an isomorphism whenever (Push) is one for the proper part `g` of the chosen
compactification: its open immersion contributes a formal isomorphism. -/
instance isIso_derivedLowerShriekHom
    [IsIso (derivedPushHom a (HasCompactification.compactification f).g)] :
    IsIso (derivedLowerShriekHom a f) := by
  unfold derivedLowerShriekHom
  infer_instance

end LowerShriek

end CondensedRing

end AlgebraicGeometry.ProEtale
````

Source `WeilConjectures/Compactification/Over.lean`

Git blob: `90e066d49595def8e1b038ba80cdc8a103d9ad02`; SHA-256: `77b5e62b958097e67ec5e81bdbfa75a0cc0e11e4a13226a06b8f340f51cde550`; 190 lines.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import WeilConjectures.Compactification.BaseChange

/-!

# Compactifications of morphisms over a base scheme

Let `S` be a scheme and `f : X ⟶ Y` a morphism of `S`-schemes. A compactification
`c : X ⟶[i] Z ⟶[p] Y` of `f` makes `Z` an `S`-scheme through `p ≫ (Y ↘ S)`, for which `p` and
`i` are morphisms over `S`. If `Y` is separated and of finite type over `S`, so is `Z`, the
structure morphism `p` being proper. The same applies to the base change
`Z ×_Y Y' ⟶[snd] Y'` of a compactification along a morphism of `S`-schemes `g : Y' ⟶ Y`, and
the projection `Z ×_Y Y' ⟶ Z` is a morphism over `S`.

These instances let the compactifications of morphisms between separated `S`-schemes of finite
type be used in statements on such schemes, without any hypothesis on `Z`.

The same is done in the category `Over S`: for a morphism `f : X ⟶ Y` of `Over S` and a
compactification `c` of the underlying morphism of schemes `f.left`, `Z` is an object
`c.overObj` of `Over S`, and `i` and `p` are morphisms `c.overI : X ⟶ c.overObj` and
`c.overG : c.overObj ⟶ Y` of `Over S`, with `c.overI ≫ c.overG = f`. For a cartesian square
`sq : IsPullback g' f' f g` of `Over S`, the square of underlying schemes is cartesian
(`CategoryTheory.IsPullback.overLeft`), and the proper and open-immersion squares of the base
change `c.baseChange sq.overLeft` are cartesian squares of `Over S`
(`Compactification.overBaseChange_isPullback_g`, `Compactification.overBaseChange_isPullback_i`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

variable {S X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The compactification `Z` of a morphism of `S`-schemes is an `S`-scheme, through the structure
morphism `p : Z ⟶ Y` followed by `Y ↘ S`. -/
instance overZ [Y.Over S] : c.Z.Over S :=
  OverClass.ofHom (c.g ≫ Y ↘ S)

instance isOver_g [Y.Over S] : c.g.IsOver S :=
  ⟨rfl⟩

instance isOver_i [X.Over S] [Y.Over S] [f.IsOver S] : c.i.IsOver S :=
  ⟨by
    change c.i ≫ c.g ≫ Y ↘ S = X ↘ S
    rw [← Category.assoc, ← c.comm]
    exact comp_over f S⟩

instance locallyOfFiniteType_over [Y.Over S] [LocallyOfFiniteType (Y ↘ S)] :
    LocallyOfFiniteType (c.Z ↘ S) :=
  inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y ↘ S))

instance quasiCompact_over [Y.Over S] [QuasiCompact (Y ↘ S)] : QuasiCompact (c.Z ↘ S) :=
  inferInstanceAs (QuasiCompact (c.g ≫ Y ↘ S))

instance isSeparated_over [Y.Over S] [IsSeparated (Y ↘ S)] : IsSeparated (c.Z ↘ S) :=
  inferInstanceAs (IsSeparated (c.g ≫ Y ↘ S))

section BaseChange

variable {Y' : Scheme.{u}} (g : Y' ⟶ Y)

/-- The fibre product `Z ×_Y Y'` underlying the base change of a compactification along a
morphism `g : Y' ⟶ Y` of `S`-schemes is an `S`-scheme through the second projection, as the
compactification scheme of the base change (`Compactification.overZ`). -/
noncomputable instance overPullback [Y'.Over S] : (pullback c.g g).Over S :=
  OverClass.ofHom (pullback.snd c.g g ≫ Y' ↘ S)

/-- The projection `Z ×_Y Y' ⟶ Z` is a morphism over `S`. -/
instance isOver_pullback_fst [Y.Over S] [Y'.Over S] [g.IsOver S] :
    (pullback.fst c.g g).IsOver S :=
  ⟨by
    change pullback.fst c.g g ≫ c.g ≫ Y ↘ S = pullback.snd c.g g ≫ Y' ↘ S
    rw [pullback.condition_assoc, comp_over g S]⟩

instance locallyOfFiniteType_pullback_over [Y'.Over S] [LocallyOfFiniteType (Y' ↘ S)] :
    LocallyOfFiniteType (pullback c.g g ↘ S) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd c.g g ≫ Y' ↘ S))

instance quasiCompact_pullback_over [Y'.Over S] [QuasiCompact (Y' ↘ S)] :
    QuasiCompact (pullback c.g g ↘ S) :=
  inferInstanceAs (QuasiCompact (pullback.snd c.g g ≫ Y' ↘ S))

instance isSeparated_pullback_over [Y'.Over S] [IsSeparated (Y' ↘ S)] :
    IsSeparated (pullback c.g g ↘ S) :=
  inferInstanceAs (IsSeparated (pullback.snd c.g g ≫ Y' ↘ S))

end BaseChange

/-! ### Compactifications of morphisms in the category over `S` -/

section OverCategory

variable {S : Scheme.{u}} {X Y : Over S} {f : X ⟶ Y} (c : Compactification f.left)

/-- The compactification `Z` of a morphism `f` of `Over S` as an object of `Over S`, through the
structure morphism `p : Z ⟶ Y` followed by `Y ⟶ S`. -/
noncomputable def overObj : Over S :=
  Over.mk (c.g ≫ Y.hom)

/-- The open immersion `i : X ⟶ Z` of a compactification of a morphism `f` of `Over S`, as a
morphism of `Over S`. -/
noncomputable def overI : X ⟶ c.overObj :=
  Over.homMk c.i (by
    change c.i ≫ c.g ≫ Y.hom = X.hom
    rw [← Category.assoc, ← c.comm, Over.w])

/-- The proper morphism `p : Z ⟶ Y` of a compactification of a morphism `f` of `Over S`, as a
morphism of `Over S`. -/
noncomputable def overG : c.overObj ⟶ Y :=
  Over.homMk c.g rfl

@[simp] lemma overObj_left : c.overObj.left = c.Z := rfl

@[simp] lemma overObj_hom : c.overObj.hom = c.g ≫ Y.hom := rfl

@[simp] lemma overI_left : c.overI.left = c.i := rfl

@[simp] lemma overG_left : c.overG.left = c.g := rfl

@[reassoc]
lemma overI_overG : c.overI ≫ c.overG = f :=
  Over.OverMorphism.ext c.comm.symm

instance isOpenImmersion_overI : IsOpenImmersion c.overI.left :=
  c.isOpenImmersion

instance isProper_overG : IsProper c.overG.left :=
  c.isProper

instance locallyOfFiniteType_overObj [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType c.overObj.hom :=
  inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y.hom))

instance quasiCompact_overObj [QuasiCompact Y.hom] : QuasiCompact c.overObj.hom :=
  inferInstanceAs (QuasiCompact (c.g ≫ Y.hom))

instance isSeparated_overObj [IsSeparated Y.hom] : IsSeparated c.overObj.hom :=
  inferInstanceAs (IsSeparated (c.g ≫ Y.hom))

section BaseChange

variable {X' Y' : Over S} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The square of underlying schemes of a cartesian square in `Over S` is cartesian. -/
theorem _root_.CategoryTheory.IsPullback.overLeft (sq : IsPullback g' f' f g) :
    IsPullback g'.left f'.left f.left g.left :=
  sq.map (Over.forget S)

variable (sq : IsPullback g' f' f g)

/-- The projection `Z ×_Y Y' ⟶ Z` from the base change of a compactification along a cartesian
square of `Over S`, as a morphism of `Over S`. -/
noncomputable def overBaseChangeFst : (c.baseChange sq.overLeft).overObj ⟶ c.overObj :=
  Over.homMk (pullback.fst c.g g.left) (by
    change pullback.fst c.g g.left ≫ c.g ≫ Y.hom = pullback.snd c.g g.left ≫ Y'.hom
    rw [pullback.condition_assoc, Over.w])

@[simp] lemma overBaseChangeFst_left :
    (c.overBaseChangeFst sq).left = pullback.fst c.g g.left := rfl

/-- The proper square of the base-changed compactification is cartesian in `Over S`. -/
theorem overBaseChange_isPullback_g :
    IsPullback (c.overBaseChangeFst sq) (c.baseChange sq.overLeft).overG c.overG g :=
  IsPullback.of_map (Over.forget S) (Over.OverMorphism.ext pullback.condition)
    (c.baseChange_isPullback_g sq.overLeft)

/-- The open-immersion square of the base-changed compactification is cartesian in `Over S`. -/
theorem overBaseChange_isPullback_i :
    IsPullback g' (c.baseChange sq.overLeft).overI c.overI (c.overBaseChangeFst sq) :=
  IsPullback.of_map (Over.forget S)
    (Over.OverMorphism.ext (c.baseChange_isPullback_i sq.overLeft).w)
    (c.baseChange_isPullback_i sq.overLeft)

end BaseChange

end OverCategory

end AlgebraicGeometry.Compactification
````

Source `WeilConjectures/CategoryTheory/RingObjects/Condensed/ContinuousMap.lean`

Git blob: `daf551011d86aad7061a3bc09d1ac98b980fac6d`; SHA-256: `08d24b1ce4129140e90e4ce64330f8d41bc63c277c515652277e835b467ae602`; 196 lines.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Condensed.TopComparison
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Mathlib.Topology.ContinuousMap.Algebra
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Limits

/-!

# The condensed ring of continuous maps into a topological ring

The *pro-étale site of a point* `*_proét` is the category `Profinite` of profinite sets with the
coherent topology, in which a finite family `{Sᵢ ⟶ S}` covers precisely when `∐ᵢ Sᵢ ⟶ S` is
surjective. A *condensed ring* is a sheaf of rings on this site.

Let `T` be a topological ring. This file defines the condensed ring `T̲` *by its sections*,
```
T̲(S) := C(S, T),
```
with restriction maps given by precomposition and the pointwise ring operations, following
Definition 2.2 of `WeilConjectures/RefactorInstruction.tex`. No limit, colimit or localization
enters this definition; such descriptions of particular coefficient rings are comparison
results, to be proved separately.

The sheaf axiom is checked directly (Proposition 2.3 of the notes): a covering is equivalent,
for the sheaf axiom, to a surjection `q : S' ⟶ S` of profinite sets, which is a topological
quotient map, so a continuous map `S' → T` descends along `q` exactly when it is constant on
the fibres of `q`. This is mathlib's `equalizerCondition_yonedaPresheaf`, and the finite
coproduct condition is formal.

A continuous ring homomorphism `T →+* T'` induces a morphism of condensed rings `T̲ ⟶ T̲'`, by
postcomposition (`Profinite.continuousMapRingSheafMap`). The underlying abelian sheaf of `T̲` is
a ring object of the category of abelian sheaves on `*_proét`
(`CategoryTheory.Sheaf.monObj_sheafCompose_obj`), commutative when `T` is.

## Main definitions

* `Profinite.continuousMapRingPresheaf`: the presheaf of rings `S ↦ C(S, T)` on `Profinite`.
* `Profinite.continuousMapRingSheaf`: the condensed ring `T̲`, a sheaf of rings for the coherent
  topology on `Profinite`, and `Profinite.continuousMapRingObj`: the underlying ring object of
  condensed abelian groups.
* `Profinite.continuousMapRingSheafMap`: the morphism of condensed rings induced by a continuous
  ring homomorphism `T →+* T'`.

## Universes

The category `Profinite.{u}` has `Hom`-types in `Type u` and objects in `Type (u + 1)`, so
sheaves on it take values in `RingCat.{u + 1}` and `Ab.{u + 1}`, matching the convention for the
small pro-étale site of a scheme `X : Scheme.{u}` in the `SixFunctors` folder. The sections
`C(S, T)`, which live in `Type u` for `T : Type`, are therefore lifted to `Type (u + 1)`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace Profinite

section Ring

variable (T : Type) [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

/-- The presheaf of rings `S ↦ C(S, T)` of continuous maps into the topological ring `T` on the
category of profinite sets, with restriction by precomposition and the pointwise ring
operations, lifted to `Type (u + 1)`. -/
noncomputable def continuousMapRingPresheaf : Profinite.{u}ᵒᵖ ⥤ RingCat.{u + 1} where
  obj S := RingCat.of (ULift.{u + 1} C(S.unop, T))
  map f := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ContinuousMap.compRightAlgHom ℤ T f.unop.hom.hom).toRingHom).comp
        ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

lemma continuousMapRingPresheaf_obj (S : Profinite.{u}ᵒᵖ) :
    (continuousMapRingPresheaf T).obj S = RingCat.of (ULift.{u + 1} C(S.unop, T)) :=
  rfl

lemma continuousMapRingPresheaf_map_apply {S S' : Profinite.{u}ᵒᵖ} (f : S ⟶ S')
    (a : ULift.{u + 1} C(S.unop, T)) :
    (continuousMapRingPresheaf T).map f a = ULift.up (a.down.comp f.unop.hom.hom) :=
  rfl

/-- The presheaf of types underlying `continuousMapRingPresheaf T` is mathlib's presheaf
`S ↦ C(S, T)` of continuous maps on `Profinite` (`ContinuousMap.yonedaPresheaf`), lifted by one
universe. -/
noncomputable def continuousMapRingPresheafForgetIso :
    continuousMapRingPresheaf.{u} T ⋙ forget RingCat.{u + 1} ≅
      ContinuousMap.yonedaPresheaf Profinite.toTopCat.{u} T ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

omit [Ring T] [IsTopologicalRing T] in
/-- The presheaf `S ↦ C(S, T)` of continuous maps is a sheaf for the coherent topology on
`Profinite`: continuous maps descend along surjections of profinite sets, which are quotient
maps, and the finite coproduct condition is formal. -/
lemma isSheaf_yonedaPresheaf :
    Presheaf.IsSheaf (coherentTopology Profinite.{u})
      (ContinuousMap.yonedaPresheaf Profinite.toTopCat.{u} T) := by
  rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
  refine ⟨inferInstance, ?_⟩
  apply +allowSynthFailures equalizerCondition_yonedaPresheaf Profinite.toTopCat.{u} T
  intro Z B π hπ
  exact .of_surjective_continuous (((Profinite.effectiveEpi_tfae π).out 0 2).mp hπ)
    π.hom.hom.continuous

/-- The presheaf `S ↦ C(S, T)` is a sheaf of rings for the coherent topology on `Profinite`. -/
lemma isSheaf_continuousMapRingPresheaf :
    Presheaf.IsSheaf (coherentTopology Profinite.{u}) (continuousMapRingPresheaf T) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget RingCat.{u + 1}),
    Presheaf.isSheaf_of_iso_iff (continuousMapRingPresheafForgetIso T),
    isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
    ← isSheaf_iff_isSheaf_of_type]
  exact isSheaf_yonedaPresheaf T

/-- The condensed ring `T̲` of continuous maps into the topological ring `T`: the sheaf of rings
`S ↦ C(S, T)` on the pro-étale site of a point, with restriction by precomposition and the
pointwise ring operations. -/
noncomputable def continuousMapRingSheaf :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  ⟨continuousMapRingPresheaf T, isSheaf_continuousMapRingPresheaf T⟩

lemma continuousMapRingSheaf_obj :
    (continuousMapRingSheaf.{u} T).obj = continuousMapRingPresheaf T :=
  rfl

/-- The condensed ring `T̲ = C(-, T)` as a ring object of condensed abelian groups: the abelian
sheaf underlying `continuousMapRingSheaf T`, with the ring object structure
`CategoryTheory.Sheaf.monObj_sheafCompose_obj`. -/
noncomputable abbrev continuousMapRingObj : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (continuousMapRingSheaf T)

variable {T} {T' : Type} [TopologicalSpace T'] [Ring T'] [IsTopologicalRing T']
  (φ : T →+* T') (hφ : Continuous φ)

/-- Postcomposition with a continuous ring homomorphism `φ : T →+* T'`, as a morphism of
presheaves of rings `C(-, T) ⟶ C(-, T')` on `Profinite`. -/
noncomputable def continuousMapRingPresheafMap :
    continuousMapRingPresheaf.{u} T ⟶ continuousMapRingPresheaf T' where
  app _ := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((φ.compLeftContinuous _ hφ).comp ULift.ringEquiv.toRingHom))
  naturality _ _ _ := rfl

lemma continuousMapRingPresheafMap_app_apply (S : Profinite.{u}ᵒᵖ)
    (a : ULift.{u + 1} C(S.unop, T)) :
    (continuousMapRingPresheafMap φ hφ).app S a = ULift.up ((⟨φ, hφ⟩ : C(T, T')).comp a.down) :=
  rfl

/-- Postcomposition with a continuous ring homomorphism `φ : T →+* T'`, as a morphism of
condensed rings `T̲ ⟶ T̲'`. -/
noncomputable def continuousMapRingSheafMap :
    continuousMapRingSheaf.{u} T ⟶ continuousMapRingSheaf T' :=
  ⟨continuousMapRingPresheafMap φ hφ⟩

lemma continuousMapRingSheafMap_hom :
    (continuousMapRingSheafMap.{u} φ hφ).hom = continuousMapRingPresheafMap φ hφ :=
  rfl

/-- Postcomposition with the identity is the identity. -/
lemma continuousMapRingSheafMap_id :
    continuousMapRingSheafMap.{u} (RingHom.id T) continuous_id = 𝟙 _ :=
  rfl

/-- Postcomposition is compatible with composition of continuous ring homomorphisms. -/
lemma continuousMapRingSheafMap_comp {T'' : Type} [TopologicalSpace T''] [Ring T'']
    [IsTopologicalRing T''] (ψ : T' →+* T'') (hψ : Continuous ψ) :
    continuousMapRingSheafMap.{u} (ψ.comp φ) (hψ.comp hφ) =
      continuousMapRingSheafMap φ hφ ≫ continuousMapRingSheafMap ψ hψ :=
  rfl

end Ring

section CommRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

/-- The condensed ring of continuous maps into a commutative topological ring is a commutative
ring object of the category of abelian sheaves on `Profinite`. -/
instance isCommMonObj_continuousMapRingObj : IsCommMonObj (continuousMapRingObj.{u} T) :=
  Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (continuousMapRingSheaf T) fun S (a b : ULift.{u + 1} C(S.unop, T)) ↦ mul_comm a b

end CommRing

end Profinite
````

Source `WeilConjectures/CategoryTheory/RingObjects/Condensed/FiniteSubextension.lean`

Git blob: `42d1ddf5500ccbd3f99ed00cec2139bdfd21655a`; SHA-256: `b1c188d5438cbfb2bded50cddbeb6481dc9e52cfa51422941dfcbbc651848c6a`; 173 lines.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

/-!

# The inclusions `E̲ ⟶ F̲ ⟶ ℚ̲̄_ℓ` of condensed coefficient rings

Let `ℓ` be a prime. The finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` form the directed poset
`PadicAlgCl.FiniteIntermediateField ℓ`. Each of them is a normed field, with the norm restricted
from `ℚ̄_ℓ`, so its condensed ring `E̲ = C(-, E)` is the commutative ring object
`Profinite.continuousMapRingObj E` of condensed abelian groups of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`. This file records the
inclusions between them:

* for `E ≤ F`, the inclusion `E̲ ⟶ F̲` (`Profinite.padicSubfieldRingObjMap`), postcomposition
  with the inclusion `E ⊆ F`, strictly functorial in `E ≤ F`;
* the inclusion `E̲ ⟶ ℚ̲̄_ℓ` (`Profinite.padicSubfieldRingObjToPadicAlgCl`): a continuous map
  `S → E` is a section of `ℚ̲̄_ℓ` over `S`, taking values in the finite subextension `E`;

compatibly with each other (`Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl`). All of them
are morphisms of ring objects. Their pullbacks along `p_X` are the coefficient changes
`E_X ⟶ F_X ⟶ ℚ̄_ℓ,X` on a scheme `X`.

## `ℚ̲̄_ℓ` as the colimit of the `E̲`

The inclusions `E̲ ⟶ ℚ̲̄_ℓ` form a cocone `Profinite.padicAlgClRingObjCocone` over the diagram
`E ↦ E̲` (`Profinite.padicSubfieldRingObjFunctor`) of condensed abelian groups, indexed by the
filtered poset of finite subextensions, and this cocone is a colimit
(`Profinite.isColimitPadicAlgClRingObjCocone`): `ℚ̲̄_ℓ = colim_E E̲`. This is the comparison
identity `eq:Qbar-comparison` of `WeilConjectures/RefactorInstruction.tex` (Proposition
`prop:comparison-only`); it is a theorem, not the definition of `ℚ̲̄_ℓ`, which is defined by its
sections. It holds because filtered colimits of condensed abelian groups are computed
sectionwise on profinite sets (the coverings of `*_proét` being refined by finite ones), and
sectionwise `ℚ̲̄_ℓ(S)` is the union of the subgroups `C(S, E)` of `C(S, ℚ̄_ℓ)` by definition.

## Sorried input

* `Profinite.isColimitPadicAlgClRingObjCocone`: `ℚ̲̄_ℓ = colim_E E̲`, see above.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

instance : CoeSort (FiniteIntermediateField ℓ) Type := ⟨fun E ↦ E.1⟩

/-- The poset of finite subextensions, as a category, is filtered: it is directed and
nonempty. -/
instance : IsFiltered (FiniteIntermediateField ℓ) := isFiltered_of_directed_le_nonempty _

end PadicAlgCl

namespace Profinite

open AlgebraicGeometry.ProEtale PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The inclusions `E̲ ⟶ F̲` -/

/-- The inclusion `E̲ ⟶ F̲` of condensed rings, for finite subextensions `E ≤ F`: postcomposition
with the inclusion `E ⊆ F`, which is continuous for the topologies restricted from `ℚ̄_ℓ`. -/
noncomputable def padicSubfieldCondensedRingMap {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    continuousMapRingSheaf.{u} E ⟶ continuousMapRingSheaf F :=
  continuousMapRingSheafMap (IntermediateField.inclusion h).toRingHom
    (continuous_subtype_val.subtype_mk _)

/-- The inclusion `E̲ ⟶ F̲` of ring objects of condensed abelian groups, for finite subextensions
`E ≤ F`: the abelian sheaf morphism underlying `Profinite.padicSubfieldCondensedRingMap`. -/
noncomputable def padicSubfieldRingObjMap {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    continuousMapRingObj.{u} E ⟶ continuousMapRingObj F :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicSubfieldCondensedRingMap ℓ h)

instance {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    IsMonHom (padicSubfieldRingObjMap.{u} ℓ h) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (padicSubfieldCondensedRingMap ℓ h)))

lemma padicSubfieldRingObjMap_id (E : FiniteIntermediateField ℓ) :
    padicSubfieldRingObjMap.{u} ℓ (le_refl E) = 𝟙 _ := rfl

lemma padicSubfieldRingObjMap_comp {E F H : FiniteIntermediateField ℓ} (h₁ : E ≤ F)
    (h₂ : F ≤ H) :
    padicSubfieldRingObjMap.{u} ℓ (h₁.trans h₂) =
      padicSubfieldRingObjMap ℓ h₁ ≫ padicSubfieldRingObjMap ℓ h₂ := rfl

/-! ### The inclusions `E̲ ⟶ ℚ̲̄_ℓ` -/

/-- The inclusion `C(-, E) ⟶ ℚ̲̄_ℓ` of presheaves of rings on profinite sets, for a finite
subextension `E`: a continuous map `S → E`, composed with the inclusion `E ⊆ ℚ̄_ℓ`, takes values
in the finite subextension `E`. -/
noncomputable def padicSubfieldToPadicAlgClRingPresheaf (E : FiniteIntermediateField ℓ) :
    continuousMapRingPresheaf.{u} E ⟶ padicAlgClRingPresheaf ℓ where
  app S := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((((algebraMap E (PadicAlgCl ℓ)).compLeftContinuous S.unop continuous_subtype_val).codRestrict
      (PadicAlgCl.finiteIntermediateFieldValued ℓ S.unop)
      (fun a ↦ (PadicAlgCl.mem_finiteIntermediateFieldValued_iff ℓ _ _).mpr
        ⟨E.1, E.2, fun x ↦ (a x).2⟩)).comp ULift.ringEquiv.toRingHom))
  naturality _ _ _ := rfl

/-- The inclusion `E̲ ⟶ ℚ̲̄_ℓ` of condensed rings, for a finite subextension `E`. -/
noncomputable def padicSubfieldCondensedRingToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    continuousMapRingSheaf.{u} E ⟶ padicAlgClCondensedRing ℓ :=
  ⟨padicSubfieldToPadicAlgClRingPresheaf ℓ E⟩

/-- The inclusion `E̲ ⟶ ℚ̲̄_ℓ` of ring objects of condensed abelian groups, for a finite
subextension `E`: the abelian sheaf morphism underlying
`Profinite.padicSubfieldCondensedRingToPadicAlgCl`. -/
noncomputable def padicSubfieldRingObjToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    continuousMapRingObj.{u} E ⟶ padicAlgClRingObj ℓ :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicSubfieldCondensedRingToPadicAlgCl ℓ E)

instance (E : FiniteIntermediateField ℓ) :
    IsMonHom (padicSubfieldRingObjToPadicAlgCl.{u} ℓ E) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (padicSubfieldCondensedRingToPadicAlgCl ℓ E)))

/-- The inclusion `E̲ ⟶ F̲` followed by the inclusion `F̲ ⟶ ℚ̲̄_ℓ` is the inclusion
`E̲ ⟶ ℚ̲̄_ℓ`: both send a continuous map `S → E` to the same map into `ℚ̄_ℓ`. -/
@[reassoc]
lemma padicSubfieldRingObjMap_comp_toPadicAlgCl {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    padicSubfieldRingObjMap.{u} ℓ h ≫ padicSubfieldRingObjToPadicAlgCl ℓ F =
      padicSubfieldRingObjToPadicAlgCl ℓ E := by
  rw [padicSubfieldRingObjMap, padicSubfieldRingObjToPadicAlgCl,
    padicSubfieldRingObjToPadicAlgCl, ← Functor.map_comp]
  rfl


/-! ### `ℚ̲̄_ℓ` as the colimit of the `E̲` -/

/-- The diagram `E ↦ E̲` of ring objects of condensed abelian groups, indexed by the finite
subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` ordered by inclusion. -/
noncomputable def padicSubfieldRingObjFunctor :
    FiniteIntermediateField ℓ ⥤ Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} where
  obj E := continuousMapRingObj E
  map f := padicSubfieldRingObjMap ℓ (leOfHom f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The cocone over the diagram `E ↦ E̲` with vertex `ℚ̲̄_ℓ`, given by the inclusions
`E̲ ⟶ ℚ̲̄_ℓ`. -/
noncomputable def padicAlgClRingObjCocone : Cocone (padicSubfieldRingObjFunctor.{u} ℓ) where
  pt := padicAlgClRingObj ℓ
  ι :=
    { app E := padicSubfieldRingObjToPadicAlgCl ℓ E
      naturality _ _ f :=
        (padicSubfieldRingObjMap_comp_toPadicAlgCl ℓ (leOfHom f)).trans
          (Category.comp_id _).symm }

/-- **`ℚ̲̄_ℓ = colim_E E̲`**: the inclusions `E̲ ⟶ ℚ̲̄_ℓ` exhibit the condensed ring `ℚ̲̄_ℓ` as the
filtered colimit of the condensed rings `E̲` of the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, in
condensed abelian groups. See the module docstring. -/
noncomputable def isColimitPadicAlgClRingObjCocone :
    IsColimit (padicAlgClRingObjCocone.{u} ℓ) :=
  sorry

end Profinite
````

Source `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/OpenImmersionLowerShriek.lean`

Git blob: `dc16433fd43e1e0f2fca83fc8edfc99260728c93`; SHA-256: `73c0914475ae39736a8ffd22e3b8e19898dd7987df7448d2318575231ee041c3`; 98 lines.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-!

# The derived adjunction `j_! ⊣ j^*` along an open immersion, on module objects

This is the module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenImmersionLowerShriek`, for
the coefficient ring objects `Λ_X = p_X^* Λ` of a commutative condensed ring `Λ`.

For an open immersion `j : U ⟶ X` both halves of the adjunction
`ProEtale.CondensedRing.openImmersionLowerShriekUpperStarAdjunction` on module objects are
*exact*: the extension by zero `j_!` by
`ProEtale.CondensedRing.preservesHomology_openImmersionLowerShriek`, and the pullback `j^*`
by `ProEtale.CondensedRing.preservesHomology_upperStar`, since the
coefficient morphism `α_j : j^* Λ_X ⟶ Λ_U` is an isomorphism. So each of them induces a
functor on derived categories by applying it levelwise, and the two levelwise functors are
again adjoint.

As in the finite-coefficient case the adjunction is obtained where the derived formalism
provides it, namely between the *total* derived functors
(`Adjunction.derivedAdjunction`), and exactness then identifies each total derived functor
with the corresponding levelwise functor; both steps are the general
`Adjunction.mapDerivedCategoryAdjunction` and `Adjunction.mapDerivedCategoryPlusAdjunction` of
`WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`. In particular the derived pullback
`L((j)^*⟦Λ⟧)` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` is,
for an open immersion, the levelwise functor `D((j)^*⟦Λ⟧)`
(`ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion`).

## Main results

- `ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion`:
  `L((j)^*⟦Λ⟧) ≅ D((j)^*⟦Λ⟧)` for an open immersion `j`.

- `ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction` and
  `ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus`: the
  derived adjunctions `D((j)_!open⟦Λ⟧) ⊣ D((j)^*⟦Λ⟧)` and `D+((j)_!open⟦Λ⟧) ⊣ D+((j)^*⟦Λ⟧)`.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For an open immersion `j : U ⟶ X`, the pullback `j^*` on module objects is exact, so its
total left derived functor `L((j)^*⟦Λ⟧)`, computed via K-flat resolutions, is canonically
isomorphic to the levelwise functor `D((j)^*⟦Λ⟧)`. -/
noncomputable def leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion :
    L((j)^*⟦Λ⟧) ≅ D((j)^*⟦Λ⟧) :=
  (j)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory

/-- The derived adjunction `j_! ⊣ j^*` along an open immersion `j : U ⟶ X` on the unbounded
derived categories of module objects over `Λ`: since both `j_!` and `j^*` are exact on
module objects, their total derived functors are the levelwise functors, and the adjunction
between the total left derived functor of `j_!` and the total right derived functor of `j^*`
becomes an adjunction between the levelwise functors. -/
noncomputable def derivedOpenImmersionLowerShriekUpperStarAdjunction :
    D((j)_!open⟦Λ⟧) ⊣ D((j)^*⟦Λ⟧) :=
  (openImmersionLowerShriekUpperStarAdjunction Λ j).mapDerivedCategoryAdjunction

/-- The bounded below version of
`ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction`: the derived
adjunction `j_! ⊣ j^*` along an open immersion on the bounded below derived categories of
module objects, obtained by restricting the unbounded one along the fully faithful inclusions,
which is legitimate since the exact functors `j_!` and `j^*` preserve bounded below objects. -/
noncomputable def derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus :
    D+((j)_!open⟦Λ⟧) ⊣ D+((j)^*⟦Λ⟧) :=
  (openImmersionLowerShriekUpperStarAdjunction Λ j).mapDerivedCategoryPlusAdjunction

instance : D((j)_!open⟦Λ⟧).IsLeftAdjoint :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).isLeftAdjoint

instance : D((j)^*⟦Λ⟧).IsRightAdjoint :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).isRightAdjoint

end AlgebraicGeometry.ProEtale.CondensedRing
````


## Second reading by NG

This is an independent reading of the repaired split, with the sandbox nodes, the current shared DAG statements, and the source exhibits open. I reread delivery-errors B–E, GOAL.md, coord/dag-sync.md, the worker/stage-1 contract and the purity-transport unit. Independently queried the read-only remote source object store at commit 7347520d9b0d17cc31d0fc34ea20f1381a83fe13: all eleven source exhibits have exactly the recorded SHA-256 hashes. UpperShriek lines 100–118 and 128–146 give the stated chosen proper-right-adjoint/open-pullback composite and its adjunction; the category and coefficient exhibits give the bounded constructible module category with no completeness requirement and the finite-extension-valued Omega ring. The comparison remains an agent-formulated obligation, not a source theorem or a finished master proof. The item’s existing STATEMENT-DISPUTED explanation and its parent-applicable single-degree repair are retained.

- Step 1 — Checked BS 6.6.11, Stacks 01T6 (morphisms.tex, lemma-finite-type-noetherian), and all eight cited statements: the finite cover of local perfect representatives gives one Tor interval, detected by the cited covering and ringed open/closed statements; PASS. A field is Noetherian; finite-type schemes have the required finite cover and dimension; no arbitrary pro-etale geometric-stalk conservativity is used.
- Step 2 — Checked BS 6.7.18, the finite geometric node’s q/b and counit formulas, semilinear-derived-sections and cartesian-section-adjoint-mates: the latter’s hypotheses are enhanced exact F, coherent invertible q, and invertible b on the stated finite-Tor domains, all supplied here; PASS.
- Step 3 — Checked Stacks 0118 (homology.tex, section-truncations), def-kun-truncations and componentwise exactness in semilinear-derived-sections: both truncation arrows are quasi-isomorphisms when only H^r survives, H^r(phi) is an actual diagram map, and conjugation evaluates to phi; PASS after clarifying naturality. Checked the immutable parent’s strict twist tower and finite-smooth-adjunction-general-base: r=-2d and its quotient compatibility supply precisely case (b).
- Step 4 — Read the complete gamma/projection identities in derived-system-evaluation-calculus, the mapping-system adjunction, the new alpha and integral completeness definition: the normalized second argument and integral test reductions satisfy their hypotheses; taking Rlim then H^0 gives the stated Hom bijection and the specified counit; PASS.
- Step 5 — Checked rational-category’s actual localized Hom groups, rational-transport’s extension of transformations, J’s equivalence and essential surjectivity, and the new compact-support a: tensoring inverse linear bijections and conjugating gives representation for every E-stage test object; PASS.
- Step 6 — Checked finite-free-completed-scalar-comparison’s actual completion map, integral-scalar-extension-constructible, stratified-perfect-characterization, finite q/b/mixed counit coherences and compact-support scalar comparison: PASS after writing the actual enhanced extension of theta and explicitly using case (a), including after a nonflat finer quotient. Cofinality S/t^nS=S/v^(en) and the quotient cocycle give independence of the chosen n with en>=m.
- Step 7 — Checked the two-colimit node’s explicit common-finite-overfield Hom description, eventual equality and object descent, and the new compact-support projection comparison: the compatible inverse bijections induce inverse colimit maps for every Omega test object; PASS. No claim of full faithfulness of one extension E to Omega is used.
- Step 8 — Checked exact master UpperShriek as above and both new nodes’ refinement/counit coherences: transpose t into the chosen adjoint, obtain a right inverse by surjectivity and a left inverse by injectivity, and compare refinement transposes; PASS. Naturality is for actual compatible coherent-system morphisms; the added text states precisely the compatibility needed and the common-degree case where level squares imply it.
- Step 9 — Checked J’s derived coefficient-extension description and condensed-flat-coefficient-calculus: tensor multiplication and b to b tensor 1 give the unit comparison; exact termwise coefficient extension and J give shifts; PASS.
- New node lem-pur-finite-coefficient-adjoint-comparisons — Read BS 6.7.16–18 and SGA4 XVIII 3.1.4/3.1.12.1, including that 3.1.12.1 is restriction of scalars, not derived extension. The source field, separated finite-type geometry, positive quotient indices, finite-Tor/etale-origin domains and transported ordinary adjoint are explicit. Finite-free and enhanced coherence clauses are honestly additional obligations. The mate and unit equations type-check. Statement-only, self-contained, definition dependencies and source places present; PASS. Existing finite-exceptional, finite-free-extension, finite-adjunction-diagram-realization, pur-etale-coefficient-system-adjoint, ctf-stability and exceptional-inverse-image all fix the algebraic closure of a finite field; none states this arbitrary-field input. It contains no reconstructed integral or condensed exceptional comparison, so is strictly smaller than the item.
- New node lem-pur-compact-support-condensed-realization — Read BS 6.7.2/6.7.14–17 and 6.8.14–15, exact master BoundedConstructible’s compact-support composite, open-extension adjunction, Basic coefficient actions, and the strict compact-support tower node. Statement-only, all schemes/rings/functors introduced with definition nodes, and source places present; PASS. The comparison with the actual condensed composite, its system alpha and Omega projection comparison are substantive obligations, not consequences silently inferred from J. Existing integral-compact-support-uniform-restriction and sf-integral-compact-support-constructible provide preservation but not these comparisons; condensed-e-realization provides pullback/direct-image comparisons but not this coherent compact-support package; compact-support-integral-coefficient-comparison fixes the finite-field datum. This node asserts no exceptional functor or right adjoint and does not restate the item.

Small-case checks: f=id gives the ordinary coefficient comparisons and the identity adjunction; for an open immersion the compact-support and exceptional functors are j_! and j^* with the stated counit. Empty schemes and zero complexes give zero mapping complexes and the unique comparison; no nonempty hypothesis or dimension of the empty scheme is used. At n=1 and m=n the quotient maps/mates have the stated unit normalization. For E=F the coefficient comparisons are identity; for a ramified extension the levels en are cofinal and include every finer quotient via the displayed construction. The r=0 alternative is the ordinary heart-diagram calculation, and r=-2d includes d=0. Torsion integral objects become zero upon localization, compatibly with all Hom bijections.

Independent duplicate/attachment/search checks: ran blueprint_refs ancestor (null, as recorded), and whole-blueprint searches “compact support condensed” and “finite coefficient adjunction” (zero matches); searched the current DAG for 6.7.18, 6.8.14 and exceptional/compact-support coefficient vocabulary and read the candidates named above. Searched the done source by the item and relevant declarations and read IntegralCoefficients.lean:321 onward: it is an ordinary-etale statement with a sorry proof, not a condensed comparison attachment. Ran two independently phrased LeanFinder queries, one for each new node, plus Loogle “CategoryTheory.Adjunction, SheafOfModules” and grep “upperShriek|lowerShriek|adic.*[Cc]onstructible”. Inspected every returned signature: underived sheaf-module adjunctions and discrete/solid condensed modules do not state either node. Actual query results/digests are appended to the node search records and searches.jsonl. Two new unsplit nodes, zero Mathlib leaves; none is elementary or a duplicate.

Changes made in this second reading:

1. Clarified the meaning of morphisms of supplied coherent systems in the item and Step 3. Naturality of truncation proves automatic compatibility for data concentrated in the same r; general enhanced morphisms must commute with the actual supplied section identifications. The argument does not infer equality of arbitrary derived-system maps from their evaluations, especially between different concentration degrees. This changes no object hypothesis and imposes no additional requirement on the parent’s common-degree application.
2. Expanded Step 6 to apply enhanced coefficient extension to the actual theta from Step 3 and compose with the specified exceptional mate b. This explicitly provides case (a) after extension and finer nonflat reduction, which need not preserve concentration in a single degree.
3. Added independently run Mathlib searches and this per-step/per-node review. Retained the first worker’s “## Review by NG”, the two justified new nodes, the source exhibits and all 35 valid verbatim citation records. No Lean, compiler, Lake, build tool, live project or live launcher was modified.
