# nt-target-smooth-purity-qbar — repair for second reading

1. Files written: `dag/nodes/sec-smooth-purity/nt-target-smooth-purity-qbar.json`, the existing statement, now split into seven proof steps. No new node and no Mathlib leaf. `citations.json` contains one full verbatim current statement for each of the 47 step/node pairs. `report.md` is this report. Other sandbox scripts, snapshots and search logs are working material only.
2. Attachments: none. Source searches by the blueprint tag and `smoothPurityIso` found only the finite small-etale construction in `WeilConjectures/EtaleCohomology/Purity/Smooth/Basic.lean:310`. It requires the dualizing-object and tensor-formula identifications as arguments; the following finite theorem depends on geometric inputs. Neither has the target's condensed coefficient category or exact conclusion. The archived target is explicitly `sorry`, so it is not an attachment.
3. WANTED: none for this split. Existing DAG statements supply the named comparison obligations; their archive/blueprint sources and the exact-master source exhibits below are available. No claim that Bhatt–Scholze literally states the condensed-adjoint reconstruction theorem is made.
4. The returned point was correct: `sk-thm-sp-qbar` states an adjunction in a common-stage category and supplies no condensed functor comparison. Moreover its current DAG statement assumes the finite-field datum; this does not cover the target's arbitrary original field. Neither mismatch is repaired by refreshing a citation quote. The target statement and hypotheses are unchanged.
5. Unfinished work: no part of the one-level split remains. The existing child nodes remain obligations at their own stage. This report makes no claim that the target or its children have finished Lean proofs. The next worker must independently read and deliver; this worker runs only `--no-push`.

## Repair against the returned head and current main

I read the maintainer's complete review of returned head `810b3e4531b6` from the read-only review packet and compared the retained sandbox with the current shared node. The returned six-step proof's Step 2 asserted an unsupported condensed formulation of the common-stage theorem. Current main is unsplit and retains an older finite/reconstruction proof. The retained sandbox had already developed a nine-step repair, including explicit finite diagonal/DNC and reduction calculations after noticing the newly explicit finite-field hypothesis. I retained those substantive calculations and the actual Tate endpoint. I added direct citations to the current `lem-pur-finite-coefficient-adjoint-comparisons`, so the finite functors, coefficient mates and preservation assertions agree literally with those of the reconstruction theorem. I also made the restriction of the normal-bundle invariant to a chart an explicit application of smooth base change.

The now-unused all-object common-stage realization equivalence and its compact-support descent were removed. They do not establish the missing arbitrary-field common-stage smooth adjunction. Instead Step 4 applies the existing, reviewed, generic `lem-pur-condensed-exceptional-reconstruction`, case (b), to the actual coherent single-degree unit tower built in Steps 2–3. Its statement names the exact chosen master `boundedConstructibleUpperShriek`, its composite adjunction and the reconstructed counit. Thus no exceptional functor, category, unit or counit is silently identified. This is a finite-to-adic-to-rational/Qbar unit proof along the current diagonal/DNC route.

No target statement, chapter/unit record or maintainer-owned field was changed. The supplied role/unit metadata comes from current main when the delivery tool rebases the overlay. No Lean source was written, no compiler/Lake/build tool was run, no subagent was started, no direct git command was run, and no live/shared project or launcher file was edited.

## Sources and searches

For the target I read the module documentation and signature at `literature/upstream-master-20261016/WeilConjectures/SmoothPurity/Defs.lean:76–92`. For the chosen adjoint, category and free-module construction I read the exact-master exhibits in `coord/reports/NC/nt-target-smooth-purity-qbar.md`, especially `ModuleObject/Derived/UpperShriek.lean`, `ProEtaleModule/DerivedCategory.lean` and `ModuleObjects/Free.lean`. For the actual Tate construction I read the complete maintained exhibit in `coord/reports/maintenance/nt-target-smooth-purity-qbar.md`. The relevant complete exhibits are repeated below for the next reader; these are inherited source exhibits with their recorded hashes, not a new git export and not finished proof evidence.

For the geometric argument I read the current main-20261015 diagonal-dualizing-object proof under `sk-prop-sp-orientation`, the complete `sk-thm-dnc` statement and proof, the coefficient-reduction statement, integral-adjunction/tower reconstruction source and categorical uniqueness proof. I compared the current common-stage Qbar source and DAG statement and did not apply its finite-field conclusion. The ordinary-etale un-oriented smooth tensor/base-change and affine-coordinate counit statements, not a forbidden geometric smooth-purity trace route, supply the local finite tools. The old blueprint source files sometimes omit hypotheses now supplied explicitly by their current DAG statements; it is those current complete statements that each citation uses.

I read Stacks `sites-cohomology.tex`, labels `lemma-pullback-K-flat` (0G7E) and `lemma-pullback-tensor-product` (07A4), for the derived coefficient calculation, and `morphisms.tex`, label `lemma-finite-type-noetherian` (01T6), for Noetherianity. The covering/basis statements have their existing sources in Stacks 098I/0990 and the pro-etale point-pullback computation. No new node is sourced to a section number or an unverified tag. The geometric and enhanced reconstruction comparison inputs that are agent-formulated remain explicitly cited existing obligations; they are not relabelled as theorems of a paper.

Whole-DAG and blueprint searches for condensed exceptional comparison, diagonal dualizing object and Tate twists found existing comparison and endpoint nodes, which are reused. There is no new frontier node. The two-colimit statement is used only to specify the actual coefficient ring/category, not for six-functor or adjunction transport.

All additional Mathlib searches used the required `msearch.py NA nt-target-smooth-purity-qbar` command. LeanFinder queried the condensed smooth unit theorem and then the section/normal-bundle dualizing comparison. Hits were structure-sheaf module adjunctions, ideal-sheaf pullback identities and generic scheme limits. LeanSearch's second purity phrasing returned algebraic smoothness and formally smooth algebra lemmas. Loogle `"smoothPurity"` and the AlgebraicGeometry grep `smoothPurity|tateTwistDerived|boundedConstructibleUpperShriek` returned no hits. The item records the exact queries and actual logged results; historical searches are retained as historical records. There was no unavailable service in these five searches. No generic module pullback or ideal-sheaf identity states the condensed exceptional-image theorem, so no Mathlib match is claimed.

## Not duplicates

No new nodes. The finite-adjoint comparison and condensed reconstruction statements are existing generic tools, not renamed smooth-purity clauses. The actual condensed Tate definition differs from the existing common-stage twist definition; both are retained with their own meanings. `same_as` remains empty: the common-stage purity theorem is a different category and a different domain of ground fields.

## Review by NA

I reopened delivery-errors B–E and checked the final seven-step node against the current statements, not against their proofs or dependency lists. All non-elementary inputs are explicit `uses`, and each has a full verbatim quote in `citations.json`. There is no new unsplit-node proof, missing new-node definition, duplicate, fabricated Mathlib query or clause moved into a new node. The proof itself carries the finite diagonal/DNC and normalization argument.

Step 1: `sk-def-sfb-dc-setting` supplies exactly the arbitrary characteristic-p setting and a compactification staying in it. `prop-weil-pbc-qbar-condensed-two-colimit` defines the archived finite-extension-valued coefficient ring and the actual full bounded constructible module-object category, without a completeness condition. Only those clauses are used. `lem-weil-pbc-finite-type-over-noetherian` and `lem-kun-dimension-finite-type` apply to all schemes in the chosen compactification. A field is Noetherian by its two ideals; the coefficient unit has a finite presentation and Tor interval [0,0] by the written tensor identity. The exact chosen adjoint and its composite adjunction are expressly specified by `lem-pur-condensed-exceptional-reconstruction`. No abstract common-stage adjoint is substituted.

Step 2: I checked all fifteen cited statements. `thm-amb-etale-exceptional-adjoint` supplies the ordinary-etale adjoint; `thm-asd-smooth-tensor` gives its un-oriented rank-one unit value. `prop-asd-smooth-base-change` gives the diagonal square with W=X times_Y X and the correctly directed map p_2^*omega_f -> omega_p_1. Its inverse pulled back by Delta gives j:C(p_1,Delta)->omega_f. The same base-change statement identifies normal-bundle chart restrictions. `lem-pur-finite-coefficient-adjoint-comparisons`, `sk-prop-sf-comparison`, `lem-sf-class-compact-support-comparison` and `lem-weil-pbc-finite-ring-constructible-derived-origin` supply the exact constructible finite adjoints, preservation, full faithfulness and origin models for the displayed Hom calculation. The finite unit meets the finite-Tor hypothesis; there is no use of an optional unbounded pro-etale adjoint. `sk-def-purity-conv` defines the section invariant in this invertible-ell setting. `lem-pur-diagonal-regular-immersion` supplies the closed regular diagonal and tangent normal bundle; current `sk-thm-dnc` supplies the normalized DNC isomorphism for this smooth projection and closed section, without a finite-field assumption. `cor-amb-affine-space-adjunction`, `lem-amb-affine-space-top-trace` and `det-sp-unique-right-adjoint` compare the local coordinate adjunction with the chosen one. `lem-amb-linear-trace-invariance` gives equality on overlaps and `lem-asd-etale-finite-twist-pullback` gives the exact Tate pullbacks. The degree-shifted sheaf maps and inverse maps then glue. The composite delta=v D j^{-1} and gamma=delta^{-1} have the displayed directions. Every ordinary-etale base is Noetherian and compactifiable in the stated setting; all coefficients are A_n=Z/ell^n with ell invertible.

Step 3: I checked all ten cited statements and the actual three normalization squares. `sk-def-sp-scalar-extension` defines derived reduction and its associativity; `sk-lem-sp-reduction` supplies invertible comparisons defined by the displayed counit-mate equation. `lem-pur-finite-coefficient-adjoint-comparisons` identifies them with the exact chosen finite functors and supplies quotient/mixed coherence. `lem-coef-semilinear-derived-sections` supplies simultaneous geometric models for the exchange, tensor and adjunction constructions, so their coherence is not inferred from unrelated level maps. Reducing the DNC comparison preserves the identity at t=1, and uniqueness in `sk-thm-dnc` identifies it before restriction at t=0. For the normal-bundle map, `def-amb-p1-trace` fixes the projection of the inverse decomposition. `lem-amb-cartier-kummer-map` includes coefficient compatibility and its ordinary-etale witness; it therefore identifies both decomposition components under reduction. `lem-amb-affine-space-top-trace` fixes open restriction and ordered coordinate composition, so the counits and their counit-preserving comparisons reduce to the same maps. `lem-asd-etale-finite-twist-pullback` and `lem-pur-twist-sheaf-locally-free` give the power-transition reduction identifications. Consequently the gamma_n commute with quotient transitions and the quotient cocycle, as required, not merely levelwise existence of isomorphisms.

Step 4: I checked all seven cited statements with case (b) of `lem-pur-condensed-exceptional-reconstruction` open. The strict semilinear system is the actual root-power tensor system, concentrated in degree -2d. `lem-pur-twist-sheaf-locally-free` gives its simultaneous pro-etale trivialization, normalized reductions and completed Tate line. The definitions `def-weil-pbc-adic-coefficient-datum` and `def-weil-pbc-bounded-constructible-tower` fix the completed coefficient ring, transitions and one global adic-lisse local model. `lem-weil-pbc-reconstruction-uniform-tower` gives the total limit, its canonical reductions and derived completeness for that model. The finite-etale roots and power maps give compatible etale-origin witnesses, verifying `def-weil-pbc-bounded-constructible-complete`; the same check for L uses the free degree-zero unit model. In the reconstruction theorem the finite functors are exactly those identified in Step 2, their mates are those of Step 3, and the single common cohomological degree meets alternative (b). Its good-truncation clause supplies an actual comparison of systems, so no arbitrary derived-diagram lift or section counit is presumed. Its conclusion explicitly concerns the target chosen G and reconstructs its counit. The unit multiplication e_Y and a=c^{-1}G(e_Y^{-1}) have inverses as written; the K-flat coefficient calculation is licensed by `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. This repairs the returned category/adjunction gap directly.

Step 5: I checked all four cited statements and the exact Tate source. `sk-prop-sfb-qlbar-colimit-x` identifies the completed ring and actual coefficient inclusions. `lem-weil-pbc-condensed-point-basis-evaluation` evaluates on affine weakly contractible objects, and `lem-weil-pbc-proetale-affine-wcontractible-covering-family` supplies enough of exactly those objects. Continuous maps to a finite quotient lift on clopen fibres, and functions in the kernel divide continuously by ell^n, so the quotient is the actual constant finite coefficient sheaf. `def-pur-condensed-tate-twists` defines the free module on the abelian roots-of-unity sheaf, its power transitions and inverse limit including n=0. The written balancing maps identify these levels with mu and respect their transitions. The zero initial term has a unique cone map, so its presence does not alter the limit. This is an ordinary strict sheaf/module limit argument, not a derived lift from its evaluations.

Step 6: I checked all four cited statements, the bottom-field coefficient map, and the tensor-power recursion. `lem-weil-pbc-condensed-e-realization` says J is derived extension from the completed coefficient sheaf; `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` licenses the K-flat extension calculation. `lem-pur-twist-sheaf-locally-free` makes Z and its powers flat rank-one modules over the completed ring. The two-stage scalar multiplication and its inverse are written explicitly, so the actual U_X(M) is computed without a new category identification. `def-pur-condensed-tate-twists` gives the line, its tensor powers and degree-zero inclusion. Both balanced tensor-power maps are written and are inverse. The d=0 case is independently the identity of B_X. No tensor is silently changed from the constant Z_l sheaf to the completed coefficient ring.

Step 7: the source and target are the ambient image of the exact chosen G(B_Y) and the exact shifted `tateTwistDerived`, respectively. Composing the Step 4 and Step 6 isomorphisms and reversing them proves both inverse equations. This is elementary. The master signature requests chosen isomorphism data and no additional composition/base-change equation.

Small cases: d=0 gives the coefficient unit and shift zero, and all normal-bundle coordinate conventions have their identity interpretations; d=1 gives the root line. Empty schemes give zero module categories and unique maps. Disconnected schemes use the given pure global d. No roots are chosen over k: simultaneous trivialization is on the cited pro-etale cover. At n=1 all finite modules are rank-one residue modules; n=0 is used only for the actual target Tate tower and is the zero sheaf. The integral lattice has one completed-coefficient ring throughout. A non-finite, imperfect or non-algebraically-closed k does not violate any cited domain. The coefficient ring always consists of finite-extension-valued functions.

No corrected target statement or source dispute is needed. The inapplicable finite-field Qbar theorem is recorded as an invalid application and removed, not weakened. There are no new statements to test for false small cases. The overlay traversal detects no path from a descendant back to this item; unrelated inherited missing descendants are not edited. `proof_deps` is the exact union of step uses. Off-unit generic tools are declared in `split_report.tool_uses` for maintainer judgment; the top-level accepted list is untouched.

## Validation and handoff

The required validation is `python3 /home/ubuntu/weil-launcher-nt/deliver.py NA nt-target-smooth-purity-qbar --no-push`. READY is issued only after it prints OK for this final sandbox. No push is authorized for this worker. The wrapper constructs its reviewable overlay on current main in its own temporary worktree; its preflight performs the project checks without a Lean compile.

## Exact-master source exhibits for the next reader

These complete exhibits are copied from the existing maintained source records, at recorded master commit `7347520d9b0d17cc31d0fc34ea20f1381a83fe13`. Their upstream `sorry` declarations specify the intended API and do not certify any mathematical theorem. The mathematical proof cites the corresponding current DAG statements separately.

Source `WeilConjectures/TateTwist/ProEtale.lean`

Git blob: `b26295f63a04264246319a1fd5f8b4f6421eb78c`; SHA-256: `b9554907baced298abbb0648fe084ac9eaffcf576c4e03e6f26a90ff3f0fff2f`.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.TateTwist.RootsOfUnity

/-!

# Tate twists of the `ℚ̄_ℓ`-sheaf on the pro-étale site

Let `ℓ` be a prime and `X` a scheme. This file constructs the Tate twists `ℚ̄_ℓ,X(d)`,
`d ∈ ℤ`, as module objects over the coefficient ring object `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ`
(`AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) X`) of abelian
sheaves on `X_proét`, the pullback of the condensed ring `ℚ̲̄_ℓ` of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` along `p_X : X_proét ⟶ *_proét`,
following Bhatt–Scholze, *The pro-étale topology for schemes*, Section 6.8:
```
ℤ_ℓ(1) := lim_n μ_{ℓ^n},     ℚ̄_ℓ(1) := ℚ̄_ℓ ⊗_{ℤ_ℓ} ℤ_ℓ(1),
```
where `ℤ_ℓ = ℤ_ℓ,X = p_X^* ℤ̲_ℓ` is the pullback of the condensed ring `ℤ̲_ℓ = C(-, ℤ_ℓ)`.

## The construction

* The `ℤ_ℓ,X`-module `ℤ/ℓ^n(1)` is the free module `ℤ_ℓ,X ⊗ μ_{ℓ^n}` on the sheaf `μ_{ℓ^n}` of
  `ℓ^n`-th roots of unity (`AlgebraicGeometry.ProEtale.rootsOfUnitySheaf`), the tensor product
  being the sheafified tensor product of abelian sheaves. Since `μ_{ℓ^n}` is killed by `ℓ^n`, this
  is `ℤ/ℓ^n ⊗_{ℤ/ℓ^n} μ_{ℓ^n} = μ_{ℓ^n}` as an abelian sheaf, with its natural structure of a
  module over `ℤ_ℓ,X ⟶ ℤ/ℓ^n` (`AlgebraicGeometry.ProEtale.tateModuleLevel`). Taking the free
  module avoids defining the action of `ℤ_ℓ,X` on `μ_{ℓ^n}` by hand.
* `ℤ_ℓ(1)` is the limit, in the category of `ℤ_ℓ,X`-module objects, of the inverse system
  `ℤ_ℓ ⊗ μ_{ℓ^{n+1}} ⟶ ℤ_ℓ ⊗ μ_{ℓ^n}` induced by the `ℓ`-th power maps
  (`AlgebraicGeometry.ProEtale.tateModule`).
* `ℚ̄_ℓ(1)` is the extension of scalars of `ℤ_ℓ(1)` along the coefficient change
  `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X` (`AlgebraicGeometry.ProEtale.coefficientMap`), the pullback along `p_X` of the
  inclusion `ℤ̲_ℓ ⟶ ℚ̲̄_ℓ` of condensed rings (`Profinite.padicIntRingObjToPadicAlgCl`), i.e. the
  relative tensor product `ℚ̄_ℓ,X ⊗_{ℤ_ℓ,X} ℤ_ℓ(1)` (`AlgebraicGeometry.ProEtale.tateTwistOne`).
  The tensor product has to be taken over `ℤ_ℓ,X` and not over `ℤ`: `ℚ̄_ℓ ⊗_ℤ μ_{ℓ^n} = 0`, and
  `ℚ̄_ℓ ⊗_ℤ ℤ_ℓ(1)` is much larger than `ℚ̄_ℓ(1)`.
* For `d ≥ 0`, `ℚ̄_ℓ(d)` is the `d`-th tensor power of `ℚ̄_ℓ(1)` over `ℚ̄_ℓ,X`, and for `d < 0`
  it is the dual `Hom_{ℚ̄_ℓ}(ℚ̄_ℓ(-d), ℚ̄_ℓ)` (`AlgebraicGeometry.ProEtale.tateTwist`).

Finally `ℚ̄_ℓ,X(d)` is placed in degree `0` of the derived category `D(Mod_{ℚ̄_ℓ,X})`
(`AlgebraicGeometry.ProEtale.tateTwistDerived`), and the twist functor `K ↦ K(d)` on
`D(Mod_{ℚ̄_ℓ,X})` is the derived tensor product with it
(`AlgebraicGeometry.ProEtale.tateTwistFunctor`).

## Implementation notes

* The construction is functorial in nothing: the comparisons `f^* ℚ̄_ℓ,Y(d) ≅ ℚ̄_ℓ,X(d)`, the
  invertibility `ℚ̄_ℓ(d) ⊗ ℚ̄_ℓ(e) ≅ ℚ̄_ℓ(d + e)` and the local triviality of `ℚ̄_ℓ(1)` when `ℓ`
  is invertible on `X` are not stated here.
* The Galois (Frobenius) action on `ℚ̄_ℓ(1)` for `X` over a finite field, which is what
  distinguishes `ℚ̄_ℓ(d)` from `ℚ̄_ℓ` over a separably closed field, is part of the Weil sheaf
  formalism and is not considered.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory MonObj Limits

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The inclusion `ℤ̲_ℓ ⟶ ℚ̲̄_ℓ` -/

/-- The inclusion `ℤ_ℓ ⊆ ℚ_ℓ`, as a ring homomorphism into the bottom finite subextension
`ℚ_ℓ ⊆ ℚ̄_ℓ`. -/
noncomputable def padicIntToBotFiniteIntermediateField :
    ℤ_[ℓ] →+* (⟨⊥, inferInstance⟩ : PadicAlgCl.FiniteIntermediateField ℓ) :=
  (algebraMap ℚ_[ℓ] (⊥ : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))).comp PadicInt.Coe.ringHom

lemma continuous_padicIntToBotFiniteIntermediateField :
    Continuous (padicIntToBotFiniteIntermediateField ℓ) :=
  continuous_induced_rng.2
    ((continuous_algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp continuous_subtype_val)

/-- The inclusion `ℤ̲_ℓ ⟶ ℚ̲̄_ℓ` of condensed rings: a continuous map `S → ℤ_ℓ` is a section of
`ℚ̲̄_ℓ` over `S`, with values in the finite subextension `ℚ_ℓ`. -/
noncomputable def padicIntCondensedRingToPadicAlgCl :
    padicIntCondensedRing.{u} ℓ ⟶ padicAlgClCondensedRing ℓ :=
  continuousMapRingSheafMap (padicIntToBotFiniteIntermediateField ℓ)
      (continuous_padicIntToBotFiniteIntermediateField ℓ) ≫
    padicSubfieldCondensedRingToPadicAlgCl ℓ ⟨⊥, inferInstance⟩

/-- The inclusion `ℤ̲_ℓ ⟶ ℚ̲̄_ℓ` of ring objects of condensed abelian groups: the abelian sheaf
morphism underlying `Profinite.padicIntCondensedRingToPadicAlgCl`. -/
noncomputable def padicIntRingObjToPadicAlgCl :
    continuousMapRingObj.{u} ℤ_[ℓ] ⟶ padicAlgClRingObj ℓ :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicIntCondensedRingToPadicAlgCl ℓ)

instance : IsMonHom (padicIntRingObjToPadicAlgCl.{u} ℓ) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (padicIntCondensedRingToPadicAlgCl ℓ)))

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The Tate module `ℤ_ℓ(1)` -/

/-- The `ℤ_ℓ,X`-module `ℤ/ℓ^n(1) = ℤ_ℓ,X ⊗ μ_{ℓ^n}`: the free `ℤ_ℓ,X`-module on the sheaf of
`ℓ^n`-th roots of unity, where `ℤ_ℓ,X = p_X^* ℤ̲_ℓ`. As an abelian sheaf it is `μ_{ℓ^n}`, since
`μ_{ℓ^n}` is killed by `ℓ^n`. -/
noncomputable def tateModuleLevel (n : ℕ) :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) :=
  (Mod.freeFunctor _).obj (rootsOfUnitySheaf X (ℓ ^ n))

/-- The transition map `ℤ/ℓ^{n+1}(1) ⟶ ℤ/ℓ^n(1)` of the Tate module, induced by the `ℓ`-th
power map `μ_{ℓ^{n+1}} ⟶ μ_{ℓ^n}`. -/
noncomputable def tateModuleTransition (n : ℕ) :
    tateModuleLevel X ℓ (n + 1) ⟶ tateModuleLevel X ℓ n :=
  (Mod.freeFunctor _).map (eqToHom (by rw [pow_succ']) ≫ rootsOfUnitySheafPow X (ℓ ^ n) ℓ)

/-- The inverse system `n ↦ ℤ/ℓ^n(1)` of `ℤ_ℓ,X`-modules. -/
noncomputable def tateModuleSystem :
    ℕᵒᵖ ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) :=
  Functor.ofOpSequence (tateModuleTransition X ℓ)

/-- The Tate module `ℤ_ℓ(1) = lim_n μ_{ℓ^n}` on `X_proét`, as a module object over `ℤ_ℓ,X`: the
limit of the inverse system `n ↦ ℤ/ℓ^n(1)`. -/
noncomputable def tateModule :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) :=
  limit (tateModuleSystem X ℓ)

/-! ### The Tate twists `ℚ̄_ℓ(d)` -/

/-- The Tate twist `ℚ̄_ℓ,X(1) = ℚ̄_ℓ,X ⊗_{ℤ_ℓ,X} ℤ_ℓ(1)`: the extension of scalars of the Tate
module along the coefficient change `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X`. -/
noncomputable def tateTwistOne :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) :=
  (Mod.extendScalars (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) X)).obj
    (tateModule X ℓ)

/-- The non-negative Tate twists `ℚ̄_ℓ,X(d) = ℚ̄_ℓ,X(1)^{⊗ d}`, the tensor powers over `ℚ̄_ℓ,X`,
with `ℚ̄_ℓ,X(0) = ℚ̄_ℓ,X`. -/
noncomputable def tateTwistNat :
    ℕ → Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
  | 0 => 𝟙_ _
  | d + 1 => tateTwistNat d ⊗ tateTwistOne X ℓ

/-- The Tate twist `ℚ̄_ℓ,X(d)` for `d ∈ ℤ`: the tensor power `ℚ̄_ℓ,X(1)^{⊗ d}` for `d ≥ 0`, and
the dual `Hom_{ℚ̄_ℓ,X}(ℚ̄_ℓ,X(-d), ℚ̄_ℓ,X)` for `d < 0`. -/
noncomputable def tateTwist :
    ℤ → Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
  | (d : ℕ) => tateTwistNat X ℓ d
  | .negSucc d => (ihom (tateTwistNat X ℓ (d + 1))).obj (𝟙_ _)

lemma tateTwist_natCast (d : ℕ) : tateTwist X ℓ d = tateTwistNat X ℓ d := rfl

/-- The Tate twist `ℚ̄_ℓ,X(d)`, placed in degree `0` of the derived category
`D(Mod_{ℚ̄_ℓ,X})`. -/
noncomputable def tateTwistDerived (d : ℤ) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) :=
  (DerivedCategory.singleFunctor _ 0).obj (tateTwist X ℓ d)

/-- The Tate twist functor `K ↦ K(d) = K ⊗ᴸ_{ℚ̄_ℓ,X} ℚ̄_ℓ,X(d)` on `D(Mod_{ℚ̄_ℓ,X})`. -/
noncomputable def tateTwistFunctor (d : ℤ) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) :=
  tensorRight (tateTwistDerived X ℓ d)

end AlgebraicGeometry.ProEtale
````

Source `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/UpperShriek.lean`

Git blob: `197c2b7f9a750bfa107231bd4dc190d284a023c1`; SHA-256: `c27c43dce9fe3ca5742e1723242e05667eab9f7496c710376807e29490b9e245`.

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

Source `WeilConjectures/CategoryTheory/ModuleObjects/Free.lean`

Git blob: `b703bc949aa37f19272db8256d0b5c7d323b78b3`; SHA-256: `0a619e2a337d10d7944faef26d800036272cafd9cda3ec0376fbec45fcc8c8f3`.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian

/-!

# Free and finitely presented module objects

Let `C` be an abelian monoidal category whose tensor product is additive in each variable, and
`R : C` an algebra object such that `R ⊗ -` is right exact, so that `Mod C R` is abelian.

* `Mod.free R n` is the free module `R^n = R ⊕ ⋯ ⊕ R` of rank `n`.
* `Mod.IsFree R M`: `M` is isomorphic to `R^n` for some `n`.
* `Mod.IsFinitelyPresented R M`: `M` is isomorphic to the cokernel of a morphism
  `R^m ⟶ R^n` between free modules of finite rank.
* `Mod.freeFunctor R : C ⥤ Mod C R` is the free module functor `M ↦ R ⊗ M`, for any monoid
  object `R` of a monoidal category.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

section Abelian

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  (R : C) [MonObj R] [PreservesFiniteColimits (tensorLeft R)]

/-- The free module object of rank `n`. -/
noncomputable abbrev free (n : ℕ) : Mod C R :=
  ⨁ fun _ : Fin n ↦ regular R

/-- A module object is *locally free of rank `n`* in the trivial (global) sense if it is
isomorphic to `R^n`; see the geometric files for the local version. -/
def IsFree (M : Mod C R) : Prop :=
  ∃ n : ℕ, Nonempty (M ≅ free R n)

/-- A module object is *finitely presented* if it is isomorphic to the cokernel of a morphism
`R^m ⟶ R^n` between free modules of finite rank. -/
def IsFinitelyPresented (M : Mod C R) : Prop :=
  ∃ (n m : ℕ) (f : free R m ⟶ free R n), Nonempty (M ≅ cokernel f)

end Abelian

section FreeFunctor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (R : C) [MonObj R]

open MonObj

/-- The free module object structure on `R ⊗ M`: `R` acts on the left factor through its
multiplication. -/
@[instance_reducible]
def freeModObj (M : C) : ModObj R (R ⊗ M) where
  smul := (α_ R R M).inv ≫ μ ▷ M
  one_smul := by
    change η ▷ (R ⊗ M) ≫ (α_ R R M).inv ≫ μ ▷ M = (λ_ (R ⊗ M)).hom
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, MonObj.one_mul]
    simp
  mul_smul := by
    change μ ▷ (R ⊗ M) ≫ (α_ R R M).inv ≫ μ ▷ M =
      (α_ R R (R ⊗ M)).hom ≫ R ◁ ((α_ R R M).inv ≫ μ ▷ M) ≫ (α_ R R M).inv ≫ μ ▷ M
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, MonObj.mul_assoc]
    simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [associator_inv_naturality_middle_assoc]
    monoidal

/-- The free module object functor `M ↦ R ⊗ M`, left adjoint to the forgetful functor. -/
@[simps]
def freeFunctor : C ⥤ Mod C R where
  obj M := { X := R ⊗ M, mod := freeModObj R M }
  map {M N} f :=
    letI := freeModObj R M
    letI := freeModObj R N
    { hom := R ◁ f
      isModHom := ⟨by
        change ((α_ R R M).inv ≫ μ ▷ M) ≫ R ◁ f = R ◁ (R ◁ f) ≫ (α_ R R N).inv ≫ μ ▷ N
        rw [Category.assoc, ← whisker_exchange, associator_inv_naturality_right_assoc]⟩ }

end FreeFunctor

end CategoryTheory.Mod
````

Source `WeilConjectures/ConstructibleSheaf/ProEtaleModule/DerivedCategory.lean`

Git blob: `4e2c26fd4485057184d30f9e329ebffb2395e1f4`; SHA-256: `167bc109ae722728ba5032d6131529559b1bb1d913655b6a25b91c8231861eb6`.

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


## Earlier second reading (a previous round; superseded)

I independently read delivery-errors B–E, GOAL.md and coord/dag-sync.md, then the sandbox node, all cited node statements, and the current main-20261015 chapter/unit and diagonal/DNC/transport source texts. I compared the target against the exact archived `SmoothPurity/Defs.lean:76–92` and the read-only exact-master Tate and chosen-adjoint exhibits. The target has precisely the original arbitrary characteristic-p field, separated finite-type schemes, smooth pure relative dimension d in N, tensor unit, chosen compactification adjoint, and ambient shifted Tate endpoint. The source requests isomorphism data; it does not require an additional normalization equation. No statement dispute or statement change is needed. No SGA literature was used as a proof source; finite geometry follows the diagonal/DNC argument and the cited existing ordinary-etale and coefficient-comparison obligations.

- Step 1 — checked the target signature against the archived source, `sk-def-sfb-dc-setting`, the actual condensed-category clauses of `prop-weil-pbc-qbar-condensed-two-colimit`, and the Noetherian/dimension lemmas: PASS; the field is arbitrary and the exact chosen G is retained.
- Step 2 — checked every cited statement, especially the domains of `thm-asd-smooth-tensor`, `prop-asd-smooth-base-change`, `sk-thm-dnc`, and `lem-pur-finite-coefficient-adjoint-comparisons`, against the diagonal/DNC source proof: PASS; the Cartesian square has g'=p_2 and f'=p_1, the diagonal is closed regular, the normal bundle is T_{X/Y}, the two site categories are compared by bounded-below witnesses, and linear invariance identifies the chart counits before the sheaf maps glue.
- Step 3 — checked the counit-mate equation in `sk-lem-sp-reduction`, the coherent models and coefficient mates, DNC uniqueness normalized at t=1, and the actual P1 Kummer decomposition and coordinate-tower counit statements: PASS; reduction respects j, D and v separately, so it respects gamma and the quotient cocycle rather than merely giving unrelated level isomorphisms.
- Step 4 — checked case (b) of `lem-pur-condensed-exceptional-reconstruction` word for word against the strict single-degree root tower, `lem-weil-pbc-reconstruction-uniform-tower` and the completed-category definition: REPAIRED/PASS; added the existing l-adic-number and adic-lisse definitions and explicit checks of Noetherianity, finite perfect quotients, completeness and the rank-one local model. The theorem's G is the actual chosen condensed right adjoint and its counit is supplied by the theorem, not inferred from an equivalence of object classes.
- Step 5 — checked `sk-prop-sfb-qlbar-colimit-x`, the weakly contractible evaluation/covering statements and the archived free-internal-module Tate definition, and read Stacks `proetale.tex` labels `lemma-get-many-weakly-contractible` (098I) and `lemma-proetale-enough-w-contractible` (0990): PASS; the clopen lifting/division calculation gives R/ell^n, the balanced level maps respect root-power transitions, and the n=0 term is zero and imposes no extra cone condition.
- Step 6 — checked the scalar-extension clause of `lem-weil-pbc-condensed-e-realization`, the exact Tate coefficient inclusion and tensor recursion, and Stacks `sites-cohomology.tex` labels `lemma-pullback-K-flat` (0G7E) and `lemma-pullback-tensor-product` (07A4): PASS; flat one-term complexes compute both extensions, the displayed balanced maps are inverse, and the d=0 case is the coefficient unit.
- Step 7 — checked the source and target types against the exact source signature and composed the two explicitly typed isomorphisms and inverse maps: PASS; this is elementary functoriality, associativity and inverse equations.
- New nodes — NONE: the sandbox contains only the existing item; there is no new statement-only, duplicate, elementary or restatement node to remove, and no new Mathlib leaf.

Small cases independently checked: d=0, d=1, n=1, the target Tate tower's n=0 term, the empty scheme, and non-finite/imperfect ground fields. The empty case has zero module categories and unique maps; no assertion of nonzero cohomology is used. In rank zero all tensor powers and coordinate conventions give the unit. Rank one gives the usual compatible root line; no roots are selected over k. The arbitrary-field finite adjunction comparison and DNC statement cover imperfect k. The finite-field-only common-stage theorem is never applied. The ordinary-etale sites are used only on Noetherian compactifiable schemes, and full faithfulness is invoked only on bounded-below objects. Stacks `morphisms.tex`, label `lemma-finite-type-noetherian` (01T6), supplies the finiteness input; Stacks `proetale.tex`, label `lemma-compare-constructible-derived` (09AL), confirms the finite-ring constructible site comparison.

Independent source/Mathlib search: read `WeilConjectures/EtaleCohomology/Purity/Smooth/Basic.lean:310–344` in slopmaster2; its finite-etale construction takes the dualizing and tensor identifications as inputs and is not this condensed target. A new LeanFinder query, “The dualizing object of a smooth morphism with l-adic coefficients is the orientation local system in cohomological degree minus twice the dimension”, returned period-ring, algebraic-smoothness and structure-sheaf module declarations; none states this result. The independent Mathlib/AlgebraicGeometry grep `dualizing|purity|TateTwist|UpperShriek` returned zero hits. Both searches ran through the required msearch.py, are retained verbatim in searches.jsonl and recorded on the item; no Mathlib match or finished upstream proof is claimed.

Changes: (1) made Step 4's coefficient-datum hypotheses and adic-lisse model explicit, and replaced its “same global free-model argument” by the actual unit-tower checks, without a new node; (2) added its two definition citations and their full current verbatim statements, bringing citations.json to 47 step/node pairs; (3) recorded the two independent searches and corrected the report's citation/Step-2 counts. Existing worker sections, including `## Review by NA`, remain in place. The earlier worker-only prohibition on pushing in the handoff section does not apply to this authorized second-reader delivery. All edits are in this sandbox; no Lean, compiler, Lake, direct git command, subagent, shared-project write or launcher edit was used.

Validation: `python3 /home/ubuntu/weil-launcher-nt/deliver.py NA nt-target-smooth-purity-qbar --no-push` printed `OK (not pushed) deliver/NA/nt-target-smooth-purity-qbar at c7944cc6c5: preflight passed`. The authorized final delivery runs the same preflight again on the fetched base; its command output supplies the delivered commit.


## Source verification repair for F1/F2/C4

The returned review identified that the NA report did not itself carry complete exact-master exhibits for the target definition, the coefficient-category interface, and the two-colimit interface. I repaired that gap here. I read the target from `literature/upstream-master-20261016/WeilConjectures/SmoothPurity/Defs.lean` (the archive is the exact target blob), and read the other two complete files from the immutable read-only reference tree `/home/ubuntu/weil-newtargets-master` at the same master revision. The byte hashes are recorded below. These files contain upstream `sorry` bodies and are source/API evidence only; they are not claimed as finished proofs. The mathematical steps continue to cite the current DAG statements, and no SGA source is used as a proof input.

### Complete source: `WeilConjectures/SmoothPurity/Defs.lean`

Source bytes: `/home/ubuntu/weil-newtargets-shared/literature/upstream-master-20261016/WeilConjectures/SmoothPurity/Defs.lean`; SHA-256 `8eac98029064bdc002a3e1c36fffcb3c2c86868e492f6545774071599a7fcb9c`; master commit `7347520d9b0d17cc31d0fc34ea20f1381a83fe13` (the Basic and TwoColimit files are also present in the read-only master tree).

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.TateTwist.ProEtale

/-!

# Smooth purity for `ℚ̄_ℓ`-coefficients on the pro-étale site

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. As in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all schemes are
objects `X : Over (Spec (.of k))`, separated and of finite type over `Spec k`, and all morphisms
are morphisms `f : X ⟶ Y` of `Over (Spec (.of k))`; in particular `ℓ` is invertible on every
scheme considered. In the documentation, `X` also stands for the underlying scheme `X.left`.

Let `f : X ⟶ Y` be a morphism whose underlying morphism of schemes `f.left` is smooth of pure
relative dimension `d`. *Smooth purity* (SGA 4, Exposé XVIII, Théorème 3.2.5, and Bhatt–Scholze,
*The pro-étale topology for schemes*, Section 6.8, for `ℚ̄_ℓ`-coefficients) identifies the
exceptional inverse image of the constant coefficient object with a shifted Tate twist:
```
pur_f : Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]
```
in the derived category `D(Mod_{ℚ̄_ℓ,X})` of module objects over `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ`, the
pullback of the condensed ring `ℚ̲̄_ℓ` (`Profinite.padicAlgClRingObj ℓ`). Here `Rf^!` is
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriek` on the bounded
constructible derived categories `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` (the right adjoint of `Rf_!`, built from the
compactification of `f` chosen by Nagata's theorem), `ℚ̄_ℓ,Y` is the tensor unit of the
monoidal category `Dᵇc(Y)⟦ℚ̲̄_ℓ⟧`
(`AlgebraicGeometry.ProEtale.CondensedRing.isMonoidal_boundedConstructible`), whose underlying
complex is the tensor unit of `D(Mod_{ℚ̄_ℓ,Y})`, and `ℚ̄_ℓ,X(d)` is the Tate twist of
`WeilConjectures.TateTwist.ProEtale`. The isomorphism is stated after the inclusion
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ D(Mod_{ℚ̄_ℓ,X})`, which is fully faithful, so that the constructibility of the Tate
twists need not be recorded.

## Sorried data

`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso` is the purity isomorphism, stated as a
`@[no_expose]` definition with value `sorry`: it is a *chosen* isomorphism, which downstream
constructions (the trace map and Poincaré duality, see
`WeilConjectures/PoincareDuality/Instruction.tex`) use as data, and whose normalization they
inherit.

The isomorphism is not a canonical map whose invertibility could be stated as a proposition
with the tools currently available: classically it is the adjoint of the trace map
`Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y` of SGA 4, Exposé XVIII, whose construction (by reduction to
relative curves and the cycle class of the diagonal) is not formalized. Its intended
normalization and compatibilities — with composition of smooth morphisms, with base change,
with étale maps (where `d = 0` and `pur` is the identification `Rf^! = Lf^*`), and the
identification of the induced trace with the classical trace on `H^{2d}_c` of a smooth curve —
are therefore not stated here either.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Smooth purity -/

section Purity

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]

/-- **Smooth purity**: for a morphism `f : X ⟶ Y` of separated `k`-schemes of finite type
which is smooth of pure relative dimension `d`, the exceptional inverse image of the constant
coefficient object is the shifted Tate twist, `Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]`. This is a chosen
isomorphism: see the module docstring. -/
@[no_expose]
noncomputable def smoothPurityIso :
    ((boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
      (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))).obj ≅
      (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d) :=
  sorry

end Purity

end AlgebraicGeometry.ProEtale.CondensedRing

````

### Complete source: `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean`

Source bytes: `/home/ubuntu/weil-newtargets-master/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean`; SHA-256 `de7399b9342ff3950b27059b0cb97887d615444dad2820b5ee58d76d0e653643`; master commit `7347520d9b0d17cc31d0fc34ea20f1381a83fe13` (the Basic and TwoColimit files are also present in the read-only master tree).

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

### Complete source: `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean`

Source bytes: `/home/ubuntu/weil-newtargets-master/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean`; SHA-256 `65e045ea9e75523cdb1daa00311fcb60aa6fa6c1e0277e6ceaca7d05bb9bef36`; master commit `7347520d9b0d17cc31d0fc34ea20f1381a83fe13` (the Basic and TwoColimit files are also present in the read-only master tree).

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-!

# The bounded constructible `ℚ̄_ℓ`-complexes as the 2-colimit over the finite subextensions

Let `ℓ` be a prime and `X` a scheme. For a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
(`PadicAlgCl.FiniteIntermediateField ℓ`), let `C_E(X) = D^b_cons(X, E)` be the bounded
constructible derived category of modules over `E_X = p_X^* E̲`
(`ProEtale.BoundedConstructible (padicSubfieldRingObj X ℓ E)`, the full subcategory of the
unbounded `D(Mod_{E_X})` of `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`),
and let `C_Ω(X) = D^b_cons(X, ℚ̄_ℓ)` be the one of modules over `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ`. The
derived extensions of scalars
```
T^X_{E,F} = F_X ⊗ᴸ_{E_X} - ,   T^X_{E,Ω} = ℚ̄_ℓ,X ⊗ᴸ_{E_X} -
```
of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` are
*assumed* to preserve bounded constructibility
(`ProEtale.boundedConstructible_derivedExtendScalarsSubfield_obj`,
`ProEtale.boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj`), and hence restrict to
functors
```
ProEtale.constructibleExtendScalars h : C_E(X) ⥤ C_F(X)   (E ≤ F),
ProEtale.constructibleToPadicAlgCl E : C_E(X) ⥤ C_Ω(X),
```
compatible with each other through the transitivity of extension of scalars
(`ProEtale.constructibleToPadicAlgClCompIso`). Together these form a cocone of categories
`ProEtale.constructibleCocone X ℓ` on the directed system `E ↦ C_E(X)`, with vertex `C_Ω(X)`,
in the sense of `WeilConjectures.CategoryTheory.FilteredTwoColimit`.

The main statement, **`ℚ̄_ℓ` is a 2-colimit** (`ProEtale.constructibleCocone_isFilteredTwoColimit`),
is that this cocone is a filtered 2-colimit: the comparison functor
`2-colim_E C_E(X) ⟶ C_Ω(X)`, `(E, K_E) ↦ T^X_{E,Ω} K_E`, is an equivalence of ordinary
categories. By `CategoryTheory.CategoryCocone.IsFilteredTwoColimit` this is the conjunction of

* **(Obj)** `ProEtale.constructibleCocone_essSurjObj`: every bounded constructible
  `ℚ̄_ℓ,X`-complex `K` is isomorphic to `T^X_{E,Ω} K_E` for some finite subextension `E` and some
  bounded constructible `E_X`-complex `K_E` (descent of constructible objects);
* **(Hom)** `ProEtale.constructibleCocone_homSurj` and `ProEtale.constructibleCocone_homInj`:
  every morphism `T^X_{E,Ω} K_E ⟶ T^X_{F,Ω} L_F` in `D(Mod_{ℚ̄_ℓ,X})` is defined over some finite
  subextension `H ⊇ E, F`, and two morphisms over `H` with the same image are equal over some
  finite subextension `H' ⊇ H`. Since the bounded constructible complexes are stable under
  shifts, this includes the statement for the shifted targets `L_F[n]`, which is what the
  compatibility with the triangulated structures requires.

These are stated for a topologically noetherian `X`, the setting in which the bounded
constructible complexes form a triangulated subcategory
(`ProEtale.isTriangulated_boundedConstructible`). They are *not* formal consequences of the
identification `ℚ̄_ℓ,X ≃ colim_E E_X` of `ProEtale.isColimitPadicAlgClRingObjCocone`, and they
are false for the unbounded derived categories; see the module docstring of
`WeilConjectures.CategoryTheory.FilteredTwoColimit` for the ordinary-category model of the
2-colimit that they describe.

## Sorried input

* `ProEtale.boundedConstructible_derivedExtendScalarsSubfield_obj` and
  `ProEtale.boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj`: extension of scalars
  along `E_X ⟶ F_X` and `E_X ⟶ ℚ̄_ℓ,X` preserves bounded constructible complexes. The extension
  of scalars is exact
  (`ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap`), so it
  is computed termwise and preserves boundedness, and it sends a locally finitely
  presented module on a stratum to a locally finitely presented one, the presentation being
  tensored up.
* **(Obj)** `ProEtale.constructibleCocone_essSurjObj`: constructible descent. A bounded
  constructible `ℚ̄_ℓ,X`-complex has finitely many constructible cohomology sheaves; each is
  locally, on the strata of a stratification, finitely presented, and a finite presentation
  involves finitely many sections of `ℚ̄_ℓ,X`, which are defined over a finite subextension since
  `ℚ̄_ℓ,X = colim_E E_X` (`ProEtale.isColimitPadicAlgClRingObjCocone`). A finite Postnikov
  induction on the length of the complex then descends the complex itself, the gluing data being
  morphisms which descend by (Hom).
* **(Hom)** `ProEtale.constructibleCocone_homSurj` and `ProEtale.constructibleCocone_homInj`:
  continuity of the derived hom. For a bounded constructible first argument `K_E` and a
  bounded below second argument, `Hom_{D(Mod_{ℚ̄_ℓ,X})}(T_{E,Ω} K_E, T_{E,Ω} L_E)` is the filtered
  colimit over `H ⊇ E` of the `Hom_{D(Mod_{H_X})}(T_{E,H} K_E, T_{E,H} L_E)`: `K_E` is a finite
  extension of shifts of locally finitely presented modules, for which the derived hom into a
  filtered colimit of uniformly bounded below complexes is the filtered colimit of the derived
  homs, and `ℚ̄_ℓ,X = colim_H H_X`.

This is the input needed to transport base change theorems from finite to `ℚ̄_ℓ`-coefficients:
by (Obj) every constructible `K` is `T^X_{E,Ω} K_E`, and the compatibility of the base change
maps with the extension of scalars (built from the (Pull) and (Push) comparisons of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`) then shows that the
base change map at `K` is the extension of scalars of the one at `K_E`. This compatibility of
the base change maps of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems`
with the extension of scalars is not yet formalized.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Abelian

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The derived extensions of scalars and their transitivity -/

section ExtendScalars

/-- The derived extension of scalars `T^X_{E,F} = F_X ⊗ᴸ_{E_X} - : D(Mod_{E_X}) ⥤ D(Mod_{F_X})`
along the inclusion of finite subextensions `E ≤ F`. -/
noncomputable abbrev derivedExtendScalarsSubfield {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) :=
  L(Mod.extendScalars (padicSubfieldRingObjMap X ℓ h))

/-- The derived extension of scalars
`T^X_{E,Ω} = ℚ̄_ℓ,X ⊗ᴸ_{E_X} - : D(Mod_{E_X}) ⥤ D(Mod_{ℚ̄_ℓ,X})` along the inclusion of a finite
subextension `E` into `ℚ̄_ℓ`. -/
noncomputable abbrev derivedExtendScalarsToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ)) :=
  L(Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E))

/-- Transitivity of the derived extension of scalars: `T^X_{E,F} ⋙ T^X_{F,Ω} ≅ T^X_{E,Ω}` for
`E ≤ F`. The extensions of scalars being exact, the composite of their derived functors is the
derived functor of the composite, which is the extension of scalars along the composite
inclusion `E_X ⟶ F_X ⟶ ℚ̄_ℓ,X = E_X ⟶ ℚ̄_ℓ,X`. -/
noncomputable def derivedExtendScalarsCompIso {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsToPadicAlgCl X ℓ F ≅
      derivedExtendScalarsToPadicAlgCl X ℓ E :=
  haveI : PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h ≫
      padicSubfieldRingObjToPadicAlgCl X ℓ F)) :=
    preservesFiniteLimits_of_natIso
      (Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h)).symm
  (Functor.leftDerivedFunctorCompIso _ _).symm ≪≫
    Functor.leftDerivedFunctorNatIso _
      ((Mod.extendScalarsComp _ _).symm ≪≫
        Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h))

end ExtendScalars

/-! ### The bounded constructible categories and the functors between them -/

section Constructible

/-- The bounded constructible derived category `C_E(X) = D^b_cons(X, E)` of `E_X`-modules, for
a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
noncomputable abbrev PadicSubfieldConstructible (E : FiniteIntermediateField ℓ) : Type _ :=
  BoundedConstructible (padicSubfieldRingObj X ℓ E)

/-- The bounded constructible derived category `C_Ω(X) = D^b_cons(X, ℚ̄_ℓ)` of
`ℚ̄_ℓ,X`-modules. -/
noncomputable abbrev PadicAlgClConstructible : Type _ :=
  BoundedConstructible (padicAlgClRingObj X ℓ)

/-- Extension of scalars along `E_X ⟶ F_X` preserves bounded constructible complexes. See the
module docstring. -/
lemma boundedConstructible_derivedExtendScalarsSubfield_obj {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (hK : boundedConstructible (padicSubfieldRingObj X ℓ E) K) :
    boundedConstructible (padicSubfieldRingObj X ℓ F)
      ((derivedExtendScalarsSubfield X ℓ h).obj K) :=
  sorry

/-- Extension of scalars along `E_X ⟶ ℚ̄_ℓ,X` preserves bounded constructible complexes. See the
module docstring. -/
lemma boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj (E : FiniteIntermediateField ℓ)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (hK : boundedConstructible (padicSubfieldRingObj X ℓ E) K) :
    boundedConstructible (padicAlgClRingObj X ℓ) ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K) :=
  sorry

/-- The extension of scalars `T^X_{E,F} : C_E(X) ⥤ C_F(X)` on bounded constructible complexes,
for finite subextensions `E ≤ F`. -/
noncomputable def constructibleExtendScalars {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    PadicSubfieldConstructible X ℓ E ⥤ PadicSubfieldConstructible X ℓ F :=
  (boundedConstructible (padicSubfieldRingObj X ℓ F)).lift
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙ derivedExtendScalarsSubfield X ℓ h)
    (fun K ↦ boundedConstructible_derivedExtendScalarsSubfield_obj X ℓ h K.obj K.property)

/-- The extension of scalars `T^X_{E,Ω} : C_E(X) ⥤ C_Ω(X)` on bounded constructible complexes,
for a finite subextension `E`: the functors of the cocone whose vertex is the bounded
constructible `ℚ̄_ℓ`-complexes. -/
noncomputable def constructibleToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    PadicSubfieldConstructible X ℓ E ⥤ PadicAlgClConstructible X ℓ :=
  (boundedConstructible (padicAlgClRingObj X ℓ)).lift
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙ derivedExtendScalarsToPadicAlgCl X ℓ E)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj X ℓ E K.obj K.property)

/-- The functors to the bounded constructible `ℚ̄_ℓ`-complexes are compatible with the extensions
of scalars between finite subextensions: `T^X_{E,F} ⋙ T^X_{F,Ω} ≅ T^X_{E,Ω}` on bounded
constructible complexes, by `derivedExtendScalarsCompIso` and the full faithfulness of the
inclusion of the bounded constructible complexes. -/
noncomputable def constructibleToPadicAlgClCompIso {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    constructibleExtendScalars X ℓ h ⋙ constructibleToPadicAlgCl X ℓ F ≅
      constructibleToPadicAlgCl X ℓ E :=
  Functor.fullyFaithfulCancelRight (boundedConstructible (padicAlgClRingObj X ℓ)).ι
    ((Iso.refl ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
        (derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsToPadicAlgCl X ℓ F)) :
      (constructibleExtendScalars X ℓ h ⋙ constructibleToPadicAlgCl X ℓ F) ⋙
          (boundedConstructible (padicAlgClRingObj X ℓ)).ι ≅
        (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
          (derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsToPadicAlgCl X ℓ F)) ≪≫
      Functor.isoWhiskerLeft (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι
        (derivedExtendScalarsCompIso X ℓ h))

/-- The cocone of categories `E ↦ C_E(X)` with vertex `C_Ω(X)`: the directed system of the
bounded constructible `E`-complexes over the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, with the
extensions of scalars as transition functors, and the extensions of scalars to `ℚ̄_ℓ` as
functors to the vertex. -/
noncomputable def constructibleCocone :
    CategoryCocone (fun E : FiniteIntermediateField ℓ ↦ PadicSubfieldConstructible X ℓ E)
      (PadicAlgClConstructible X ℓ) where
  T h := constructibleExtendScalars X ℓ h
  Φ E := constructibleToPadicAlgCl X ℓ E
  iso h := constructibleToPadicAlgClCompIso X ℓ h

end Constructible

/-! ### `ℚ̄_ℓ` is a 2-colimit -/

section TwoColimit

variable [TopologicalSpace.NoetherianSpace X]

/-- **(Obj)**: every bounded constructible `ℚ̄_ℓ,X`-complex is isomorphic to the extension of
scalars `T^X_{E,Ω} K_E` of a bounded constructible `E_X`-complex `K_E` for some finite
subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. See the module docstring. -/
theorem constructibleCocone_essSurjObj : (constructibleCocone X ℓ).EssSurjObj :=
  sorry

/-- **(Hom), surjectivity**: every morphism `T^X_{E,Ω} K_E ⟶ T^X_{F,Ω} L_F` between extensions of
scalars of bounded constructible complexes is the extension of scalars of a morphism
`T^X_{E,H} K_E ⟶ T^X_{F,H} L_F` for some finite subextension `H ⊇ E, F`. See the module
docstring. -/
theorem constructibleCocone_homSurj : (constructibleCocone X ℓ).HomSurj :=
  sorry

/-- **(Hom), injectivity**: two morphisms of bounded constructible `H_X`-complexes with the same
extension of scalars to `ℚ̄_ℓ,X` have the same extension of scalars to `H'_X` for some finite
subextension `H' ⊇ H`. See the module docstring. -/
theorem constructibleCocone_homInj : (constructibleCocone X ℓ).HomInj :=
  sorry

/-- **`ℚ̄_ℓ` is a 2-colimit**: the bounded constructible derived category `D^b_cons(X, ℚ̄_ℓ)`
of `ℚ̄_ℓ,X`-modules, with the extensions of scalars from the bounded constructible derived
categories `D^b_cons(X, E)` of the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, is the filtered
2-colimit of the latter: the comparison functor `2-colim_E D^b_cons(X, E) ⟶ D^b_cons(X, ℚ̄_ℓ)`,
`(E, K_E) ↦ ℚ̄_ℓ,X ⊗ᴸ_{E_X} K_E`, is an equivalence of ordinary categories. -/
theorem constructibleCocone_isFilteredTwoColimit :
    (constructibleCocone X ℓ).IsFilteredTwoColimit where
  essSurjObj := constructibleCocone_essSurjObj X ℓ
  homSurj := constructibleCocone_homSurj X ℓ
  homInj := constructibleCocone_homInj X ℓ

end TwoColimit

end AlgebraicGeometry.ProEtale

````

## Review addendum by NA

I verified the three complete exhibits against their source files byte-for-byte by SHA-256 and reread the declarations used by the split. `Defs.lean` supplies the exact target coefficient ring, compactification-based `boundedConstructibleUpperShriek`, tensor unit, Tate endpoint, hypotheses, and isomorphism direction. `ModuleObject/Basic.lean` supplies the definition of the pulled-back condensed coefficient ring and canonical coefficient morphisms; its sorried infrastructure is recorded as reference input rather than treated as a proof. `Colimit/TwoColimit.lean` supplies the finite-subextension coefficient categories, derived scalar-extension functors, bounded-constructible preservation assumptions, cocone, and Obj/Hom two-colimit interface. I checked that Steps 1, 4, 5, and 6 use exactly these clauses and retain the target's condensed category, rather than replacing it by a common-stage or integral category. The existing `citations.json` was rechecked unchanged: every step citation remains a verbatim statement quote from its DAG node. No target statement, DAG dependency, proof step, or route source was changed.


## Constructibility definition: the singular Def.lean requested in the return

The return's `Def.lean` is also supplied in full here, in addition to the target's `Defs.lean`: `WeilConjectures/ConstructibleSheaf/ProEtaleModule/Def.lean`. I read its actual `IsLocallyFinitelyPresented` and `IsConstructible` definitions. The first requires a pro-etale covering on which the pulled-back internal module is a cokernel of a map between finite free modules; the second requires a finite stratification whose restrictions have this property. It imposes no derived completeness condition and is not defined by lisse local systems. Together with the already included `DerivedCategory.lean` exhibit, this is precisely the full bounded-cohomology subcategory used in Steps 1 and 4 and in `prop-weil-pbc-qbar-condensed-two-colimit`. The unit's local presentation in Step 1 is the rank-zero to rank-one cokernel; thus this source check does not rely on replacing finite presentation by local constancy. The integral complete category and the condensed category remain different categories, related only by the explicitly cited reconstruction/realization theorems.

Source `/home/ubuntu/weil-newtargets-master/WeilConjectures/ConstructibleSheaf/ProEtaleModule/Def.lean`; exact read-only master reference; SHA-256 `bebcdb7cadad83ef156e89d88db63fbc0f953243ce8f51139a33a590231af528`.

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

## Second reading by NA

- Item statement: checked against `WeilConjectures/SmoothPurity/Defs.lean`, declaration `AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso`, and its defining category/dependency nodes; verdict PASS, with arbitrary characteristic-p field, separated finite-type schemes, smooth pure relative dimension, chosen upper-shriek, and shifted Tate endpoint retained.
- Step 1: checked against `sk-def-sfb-dc-setting`, `prop-weil-pbc-qbar-condensed-two-colimit`, finite-type/Noetherian and dimension statements, and `lem-pur-condensed-exceptional-reconstruction`; verdict PASS, exact condensed coefficient category and chosen compactification adjoint are used.
- Step 2: checked every cited node statement against the diagonal/DNC source route, including ordinary étale adjunction, smooth tensor, base change, regular diagonal, DNC, affine trace, and finite-coefficient comparison; verdict PASS, no finite-field-only theorem is applied.
- Step 3: checked coefficient mate equations, quotient cocycle, DNC normalization, Cartier/Kummer maps, and affine trace compatibility against all ten cited statements; verdict PASS, compatibility is argued rather than asserted as transport.
- Step 4: checked the strict root-power tower, completed coefficient datum, adic-lisse local model, reconstruction hypotheses, and case (b) of `lem-pur-condensed-exceptional-reconstruction`; verdict PASS, the target chosen condensed adjoint and its counit are preserved.
- Step 5: checked the completed coefficient quotient and actual Tate tower against the coefficient, weakly contractible evaluation/covering, and Tate-definition nodes; verdict PASS, balancing maps and the zero level are explicit.
- Step 6: checked scalar extension, K-flat tensor calculation, local freeness, and tensor-power recursion against the four cited statements; verdict PASS, including the independent d=0 case.
- Step 7: checked source and target types against the upstream declaration; verdict PASS, composition and inverse equations are elementary.
- New nodes: none; the sandbox contains only the existing item node, so there are no new B1–B7 statements, Mathlib leaves, duplicates, or nodes to remove.
- Edge cases: checked d=0 and d=1, n=1 and the n=0 Tate term, empty schemes, and arbitrary imperfect/non-finite ground fields; verdict PASS.
- Independent Mathlib searches: LeanFinder query “Exceptional pullback of the unit for a smooth map is an invertible orientation sheaf shifted by twice the dimension” returned manifold vector-field declarations, `SheafOfModules.pullbackObjUnitToUnit`, and `SingularManifold.comap_f`; these are ordinary pullbacks and do not state exceptional smooth purity. The Mathlib grep `dualizingComplex|smoothPurityIso|tateModuleSystem` returned zero hits. Both exact outputs are logged and the results are recorded on the item.
- Source verification: the complete target `SmoothPurity/Defs.lean`, `ModuleObject/Basic.lean`, `ModuleObject/Colimit/TwoColimit.lean`, and `ConstructibleSheaf/ProEtaleModule/Def.lean` exhibits in this report match the read-only source files in full, byte hashes as recorded above. In particular the singular `Def.lean` required by the return is present and defines local finite presentation, rather than a substitute lisse condition.
- Changes made: added this required second-reading record and the two independent searches; no node statement, proof step, citation, or source route was changed.

Second-reading dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver.py NA nt-target-smooth-purity-qbar --no-push` printed `OK (not pushed) deliver/NA/nt-target-smooth-purity-qbar at fe45d98fab: preflight passed`. The authorized delivery repeats preflight on its freshly fetched base.
