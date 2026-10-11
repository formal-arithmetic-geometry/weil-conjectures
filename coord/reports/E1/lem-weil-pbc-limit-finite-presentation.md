## Worker report

The module states `Algebra.exists_limit_finite_presentation`, the Noetherian approximation
for a finitely presented commutative ring map. It quantifies a nonempty directed partially
ordered index type, diagrams of commutative rings, a natural transformation of models, and
cocones to the given rings. The cocones are colimits; their components commute with the
original ring map. Each model map is finite type, each base model is finite type over Z,
and each transition square and final square is a categorical pushout, rendering the tensor
base-change isomorphisms in clauses (4) and (5).

The hypotheses are rendered by `{R S : Type u}`, commutative-ring instances, and
`hφ : RingHom.FinitePresentation φ`. Clause (1) is the pair of `Nonempty (IsColimit cR)`
and `Nonempty (IsColimit cS)`; clause (2) is
`RingHom.FiniteType (algebraMap ℤ (Rfun.obj l))`; clause (3) is
`RingHom.FiniteType (η.app l).hom`; clause (4) is the transition `CategoryTheory.IsPushout`
square; clause (5) is the final pushout square with the map induced by `φ`.
The directed transition compatibility is supplied by the functors and natural
transformation, and cocone compatibility by `Cocone`.

Dependencies used: `Algebra.FinitePresentation` / `RingHom.FinitePresentation` from
`Mathlib.RingTheory.FinitePresentation`; `CategoryTheory.Limits.colimit`, `Cocone`,
`IsColimit`, and `CategoryTheory.IsFiltered` from Mathlib; `Algebra.FiniteType` /
`RingHom.FiniteType` from `Mathlib.RingTheory.FiniteType`.

Edge cases checked include empty polynomial presentations and zero generators (captured by
finite-presentation and finite-type predicates), and nonempty index sets (the explicit
`Nonempty Λ` binder). Searches: `rg` over `WeilConjectures/` found no existing statement;
Mathlib LeanSearch/LeanFinder/grep searches found only the single-model presentation
lemmas, not this directed-system theorem. The remote compiler completed with no errors or
warnings.

## Earlier second reading (a previous round; superseded)

The statement is rendered directly by the theorem signature above. The index is explicitly
nonempty and directed; `Cocone` and `IsColimit` express both colimit clauses; the natural
transformation gives the model maps and its pushout squares express the tensor base-change
maps. The final pushout square uses the original ring homorphism after transporting along
the cocone-point equalities.


## Second reading by E1

I opened the delivered node and module, all three statement dependency nodes, and
Mathlib's actual declarations. I read Stacks algebra.tex on the project server
(the literature checkout is absent on this machine): conventions lines 33–42,
Tag 00R0 at lines 32567–32590, Tag 00R1 at lines 32593–32635, and the coefficient
presentation construction of Tag 00QV at lines 32346–32400. The source assumes
commutative unital rings, explicitly allowing the zero ring. Its local-ring
hypotheses in 00QV belong to that local analogue, not to 00R0.

Objects, hypotheses and conclusions, matched item by item:

1. Arbitrary commutative rings R and S: `{R S : Type u} [CommRing R] [CommRing S]`.
   Verdict: exact within an arbitrary common ambient universe, with no domain,
   nontriviality, locality, characteristic, or Noetherian assumption.
2. Ring map φ of finite presentation: `(φ : R →+* S)` and
   `hφ : RingHom.FinitePresentation φ`. Verdict: exact. I read
   FinitePresentation.lean:44–46 and 392–393: the ring-map predicate installs
   exactly φ.toAlgebra, and asks for a finite-variable polynomial surjection
   with finitely generated kernel, as def-weil-pbc-finitely-presented-algebra
   requires. No algebra structure independent of φ is assumed.
3. A nonempty directed set Λ: existential `Λ : Type u`, `Preorder Λ`,
   `Nonempty Λ`, and `IsDirected Λ (fun a b => a ≤ b)`. Verdict: exact after
   repair. The original independent `Type v` universally quantified v and
   demanded arbitrarily small approximation systems for arbitrary R. For example,
   a small indexed colimit of finite type integer rings cannot cover a ring of
   arbitrarily larger cardinality in a larger universe. The coefficient-subring
   index is a subtype of `Subalgebra ℤ R`, so `Type u` is sufficient. Preorder
   follows the standing directed-set convention; the construction can use a poset.
4. Model rings R_λ, S_λ and their transitions: `Rfun`, `Sfun : Λ ⥤ CommRingCat`.
   Verdict: exact. The category induced by the preorder has a morphism for each
   inequality; functor laws impose identity and composition compatibility.
   The ring-category universe is constrained to u by the cocone-point equalities.
5. Model ring maps ρ_λ and their compatibility: `(η : Rfun ⟶ Sfun)` and `η.app l`.
   Verdict: exact; naturality is the transition commutative square.
6. Maps π_λ to R and κ_λ to S: `(cR : Cocone Rfun)`, `(cS : Cocone Sfun)`, the
   two point equalities, and `cR.ι.app l`, `cS.ι.app l` transported along them.
   Verdict: exact. Cocone naturality imposes transition compatibility, and the
   first universally quantified equation is κ_λ ρ_λ = φ π_λ. Quantifying over
   the equality proofs does not strengthen the condition, since they are
   proof-irrelevant; the preceding conjunction guarantees they exist.
7. Clause (1), both ring colimits: `Nonempty (IsColimit cR)` and
   `Nonempty (IsColimit cS)`. Verdict: exact. I read IsLimit.lean:62–70: desc,
   fac, and uniq give the stated universal property. This uses the recorded
   def-weil-pbc-category-colimit declarations, with existence of the universal
   cocones rather than a private definition or a pre-assumed HasColimit instance.
8. Clause (2), finite type integer base models:
   `∀ l, RingHom.FiniteType (algebraMap ℤ (Rfun.obj l))`. Verdict: exact.
   FiniteType.lean:39–40 and 217–218 define finite generation of the top
   subalgebra using precisely this ring map, as the finite-type dependency says.
9. Clause (3), finite type model maps: `∀ l, RingHom.FiniteType (η.app l).hom`.
   Verdict: exact; the algebra is induced by ρ_λ, with no stronger finite
   presentation or module finiteness conclusion.
10. Clause (4), the specified transition tensor map is an isomorphism:
    `IsPushout (η.app l) (Rfun.map (homOfLE h))
      (Sfun.map (homOfLE h)) (η.app m)` for every l ≤ m.
    Verdict: exact. I read IsPullback/Defs.lean:78–81 and
    CommRingCat.isPushout_tensorProduct (Constructions.lean:116–124).
    The tensor product is the pushout of those two maps; hence the canonical
    comparison to S_μ is an isomorphism precisely when this square is a pushout.
    On pure tensors it sends s ⊗ r to the transition image of s times ρ_μ(r).
    `Nonempty` around this Prop adds no mathematical condition.
11. Clause (5), the specified final tensor map is an isomorphism: the final
    `IsPushout (η.app l) (cR.ι.app l) (cS.ι.app l)` with the transported φ.
    Verdict: exact by the same pushout universal property; the map is specifically
    s ⊗ r ↦ κ_λ(s) φ(r), not an arbitrary isomorphism. This clause is derived
    by the node's Step 5; it is not literally a separate clause of 00R0.

Edge cases: the index is nonempty as required (an empty diagram is excluded by
both source and node); zero R, zero S, zero generators, and zero relations remain
allowed. The finite-presentation definition permits n = 0 and FG kernel zero;
no characteristic hypothesis occurs. Schemes are not objects of this statement,
so an empty scheme is irrelevant here. All variables and the sole universe u
are bound; finite coefficient subrings fit in u, including u = 0. R and S may
be placed in any common ambient universe; no fixed small universe is imposed.

Independent searches (different wording from the first worker):

- LeanFinder via msearch: “commutative ring homomorphism of finite presentation
  as directed colimit of finite type integer algebras with tensor product base
  change squares”. Eight hits, including
  RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit and
  CommRingCat.isFinitelyPresentable_hom; these factor maps through a given
  filtered system and do not construct the approximation system. I opened
  Mathlib/Algebra/Category/Ring/FinitePresentation.lean to verify the difference.
- Loogle via msearch: `"FinitePresentation", "IsColimit"`: zero hits.
  An initial query without the comma was rejected by the service parser and
  was replaced by this valid query; that rejection is not evidence of absence.
- LeanSearch via msearch: “A finitely presented ring map is a directed colimit
  of finite type integer algebra maps with all base change squares pushouts”:
  service unavailable (Internal Server Error), no absence verdict assigned.
- rg on Mathlib, WeilConjectures, repository lean/Sheaf and
  dag/lean_names_upstream.json for limit_finite_presentation,
  exists_limit_finite_presentation, Noetherian approximation, exists_limit,
  tensorModelOfHasCoeffsEquiv, and finite-presentation/colimit combinations.
  No declaration of this full statement. I opened the strongest new candidate,
  Algebra.FinitePresentation.exists_fg_subalgebra_isPushout in
  WeilConjectures/Mathlib/RingTheory/FinitePresentation.lean:35–39: it supplies
  one finitely generated integer subalgebra and one model, not the directed
  transitions or either colimit. I also read
  Algebra.Presentation.tensorModelOfHasCoeffsEquiv (Core.lean:207–214), likewise
  a single-model isomorphism. Neither can be recorded as this existing node.

Repairs: tied the index universe to the ring universe, used Preorder for the
standing directed-set convention, replaced the abbreviated proof docstring
with all six node steps and their dependency identifiers, and added the
project copyright header. No node statement or mathematical dependencies were
changed; the node's lean.statement was copied verbatim from the repaired
signature. No new definitions or dependency modules were necessary. The only
proof is the named theorem's `sorry`; no data definition or hollow hypothesis
was introduced. The remote compiler accepted the repaired signature with no
errors or warnings. The delivery dry run is run after this report is written.
