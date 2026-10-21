## Worker report

States `CategoryTheory.CommonStage.commonStage_inverse_through_karoubi` in
`Sheaf.CategoryTheory.CommonStageKaroubiInverse`. Nothing is proved: every theorem
body is `sorry`. Every definition has explicit data. The other declarations render
this same node's inner extension and coherence clauses, rather than new notions or
independent lemmas. No new or dependency nodes and no statement correction.

Sources read: the entire node and its ten proof steps; blueprint sketch 32,
lines 1291–1359 and 1412–1455 (including the preceding finite-stage definition);
the recorded coherent pair descent node and both of its reexported source modules.
The source specifies projector extension, common-stage quotient and outer Karoubi
extension. The node spells out the elementary local inverse calculation used there.

Hypotheses and constructions, in statement order:

- The prime is `(l : ℕ) [Fact l.Prime]`. The fixed closure is `K : Type w` with
  `Field`, `Algebra ℚ_[l] K`, and `IsAlgClosure ℚ_[l] K`. Every stage is exactly
  `Padic.FiniteCoefficientFields l K`, not an arbitrary filtered category.
- `A B : Diagram` supplies the raw categories, `Category`, `Preadditive`,
  `HasFiniteBiproducts`, additive transitions, literal unit equalities, specified
  associators, both normalized unit equations and pentagon. These fields were read
  in `CoherentPairFunctorDescent.lean`, including their full signatures.
- `Φ Ψ : Family A B` supplies additive raw functors and comparison isomorphisms.
  `hΦ hΨ : Family.Coherent` supplies precisely the comparison unit and tower laws.
  `η : ∀ E, Φ.φ E ⟶ Ψ.φ E` supplies stage naturality; `hη : Compatible η` is
  `bF.hom ≫ η_M = V(η_E) ≫ bG.hom`, the node's compatibility equation in Lean's
  left-to-right composition convention.
- `Diagram.innerKaroubi` has objects `Karoubi (A.C i)`, transitions `innerU`, and
  associators `innerAssoc`, all from Mathlib `functorExtension₂`. Its fields use
  named statements `innerUnit`, `innerLeft`, `innerRight`, `innerPentagon`, and
  `localInverse_extension_additive` for the node's extension assertions.
  Finite biproducts are Mathlib's `Karoubi.karoubi_hasFiniteBiproducts`.
- `Family.innerKaroubi` extends the functors and comparison isomorphisms by that
  same Mathlib construction. `innerCoherent` and `innerCompatible` state the
  node's extended tower/unit and compatibility clauses. `innerRestriction_formulas`
  explicitly gives η-plus, b-plus and inverse-b-plus as all three sandwich formulas.
  With Lean composition, `F(p) ≫ η ≫ G(p)` is the node's `G(p) η F(p)`.
- `D : DescentSystem` is the dependency's representative-characterized canonical
  pair-category operations and descent. It is not an extra assumption on raw
  categories: `coherent_pair_functor_descent l K` supplies such data for every
  closure. The theorem holds for every realization of that specification. This
  avoids selecting unrelated data from a sorried mere existence theorem.
  `localInverseFunctor` and `localInverseTransformation` use `D.descend` and
  `D.transformation`. The canonical quotient is exactly `CommonStage.Hom`, not
  a private pair category. The recorded StageSystem module publicly reexports it.
- `E`, `X`, `v`, `hav`, `hva` are the one raw stage, one raw object, one raw inverse
  and its two inverse laws. No invertibility elsewhere and no idempotent completeness
  instance is required.

Conclusions, in statement order:

- The first universal clause ranges over any inner `P : Karoubi (A.C E)` with
  `P.X = X`, thus every idempotent on X. It then ranges over any outer `Q` with
  `Q.X = localInversePair D A E P`, thus every pair-category idempotent.
  The equality binders merely identify underlying objects; setting them to `rfl`
  recovers exactly `(E,(X,p))` and its arbitrary outer projector.
- `∃ e : Fhat.obj Q ≅ Ghat.obj Q` asserts invertibility of this component.
  `e.hom = ...map (localInverseTransformation ...).app Q` identifies the actual
  transformation, rather than an unrelated isomorphism.
- `localInverseRestriction P Q f` is the composite of Mathlib's standard
  `decompId_i`, `toKaroubi.map f`, `decompId_p`; its underlying map is precisely
  `P.p ≫ f ≫ Q.p`. Therefore `localInverseClass D Ψ Φ ... v` represents
  `[E,G(p) ≫ v ≫ F(p)]`, exactly `[E,w]` in right-to-left notation.
  The first HEq specifies `e.inv.f = Gbar(q) ≫ [E,w] ≫ Fbar(q)`.
  `eqToHom` factors only carry the displayed `hP`, `hQ` endpoint identifications.
  They are identities for the literal node presentation.
- Two forward HEq clauses give both `Fbar(q) ≫ ηbar_Q ≫ Gbar(q)` and its precise
  original-stage representative. Inner restriction makes that representative
  `[E,F(p) ≫ a ≫ G(p)]`. Thus the displayed forward formula is present explicitly.
- The two following equalities give composites equal to `Fbar.map Q.p` and
  `Gbar.map Q.p`. These are the actual Karoubi identities, not raw identity maps.
  In particular `P = toKaroubi.obj X` and `Q = toKaroubi.obj (E,P)` are allowed;
  neither identity-projector case is excluded.
- For every outer `R` and `t : Q ≅ R`, the clause produces `r` with hom exactly
  the actual component at R, and formulas `Fhat(t.inv) ≫ e.hom ≫ Ghat(t.hom)`
  and `Ghat(t.inv) ≫ e.inv ≫ Fhat(t.hom)`. Reversing notation gives precisely
  the two conjugations in the node. An Iso includes both inverse equations.
- The second universal clause covers every M with E ≤ M, including M=E.
  `localInverseTransport Φ Ψ h X v` is `bG.inv ≫ V(v) ≫ bF.hom`.
  Both raw inverse equations are stated at `U(h).obj X`.
- Its two HEq clauses identify the original descended component and inverse on
  the identity inner projector with the M representatives conjugated by bF and bG.
  `localInverseStageRep` includes each raw arrow by the actual extended projectors;
  on the identity-projector object these are identity-projector inclusions.
  Because every M class equals the same E component/inverse, these clauses express
  independence of all common overfields without equating different endpoints.
- The final clause quantifies any other raw inverse v' and proves v'=v. Every
  displayed inverse construction is a function of v, so all formulas are independent
  of this choice; uniqueness of e.inv and r.inv follows from their Iso laws.

Universe check: raw categories retain independent object universe u and Hom universe v.
Karoubi objects live in `max u v`; inner diagrams and `D` use that maximum, and the
coefficient closure/index uses independent w. No equality of these universes is imposed.
All universes and variables are bound explicitly with `autoImplicit false`.

Dependency declarations used:

- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: `Padic.FiniteCoefficientFields`,
  `finiteCoefficientField_finiteDimensional`, `finiteCoefficientCompositum`,
  `finiteCoefficientBase`, `finiteCoefficientFields_properties`; full definitions,
  signatures and docstrings read. The indexing type is used through the public import.
- `Sheaf.CategoryTheory.StageSystemFunctorDescent`, reexporting
  `Sheaf.CategoryTheory.CoherentPairFunctorDescent`: `CommonStage.Diagram`, `Family`,
  `Family.Coherent`, `Compatible`, `Rep`, `PairStructure`, `DescentSystem` and all its
  canonical representation/descent/outer-extension fields. Also read the recorded
  `StageSystem.coefficientPairFunctor_exists`, which targets a different upstream
  carrier; no unusable-interface repair is needed here because its original complete
  common-stage interface is explicitly retained and reexported.
- `Mathlib.CategoryTheory.Idempotents.Karoubi`: `Idempotents.Karoubi`, `Karoubi.Hom`,
  `toKaroubi`, `Karoubi.decompId_i`, `Karoubi.decompId_p`, identity and composition
  definitions (full signatures and docstrings read).
- `Mathlib.CategoryTheory.Idempotents.FunctorExtension`: `functorExtension₂`, its
  object/map and transformation formulas, read including its implementation through
  `FunctorExtension₁`.
- `Mathlib.CategoryTheory.Idempotents.Biproducts`: `Karoubi.karoubi_hasFiniteBiproducts`.
- `Mathlib.CategoryTheory.Limits.Shapes.Biproducts`: `HasFiniteBiproducts`;
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`: `Functor.Additive`.
  Size convention is rendered by explicit independent universes as its record asks.

Edge cases checked algebraically: p=0 gives zero inner objects and zero identities;
p=1 and q=1 recover the raw inverse; q=0 gives zero outer identities; M=E uses
unit comparisons and identity transition; t=1 gives the original component;
non-split raw projectors remain formal Karoubi objects. The raw zero object is
allowed. No global inverse transformation or globally invertible η is assumed.

Searches actually run using `msearch.py NV lem-sbc-common-stage-inverse-through-karoubi`:

- leanfinder: “A compatible natural transformation invertible at one object descends
  through a common stage pair category and two Karoubi envelopes”: eight hits headed
  by `Idempotents.natTrans_eq` and extension-universal-property formulas; no exact match.
- loogle: `CategoryTheory.Idempotents.functorExtension₂`: twelve hits, including the
  exact canonical extension and object/projector/arrow/component formulas. Reused it;
  none states the common-stage local inverse result.
- grep: `Karoubi.*[Ii]so|functorExtension₂` in `CategoryTheory/Idempotents`: nine hits,
  extension modules and Karoubi universal equivalences; no exact match.
- leansearch: “A compatible natural transformation with invertible component restricts
  to idempotent summands and descends to a filtered pair category”: eight hits headed
  by `Idempotents.natTrans_eq`, `app_comp_p`, and functor-category idempotent completeness;
  no exact match.
- `rg` across both project source roots for the item id and common-stage inverse/
  Karoubi terms: only other coefficient/twist and inverse-image results, no statement
  of this result. Also searched `dag/lean_names_upstream.json` and the StageSystem
  and CategoryTheory modules for existing Karoubi extensions. The general Mathlib
  construction was reused; the project has no inner Diagram/Family extension API.

Validation: prescribed `scompile.py` compiled the complete delivered module both in
its sandbox and at its intended module name, cleanly under the 60-second limit.
Initial universe diagnostics were repaired by the `max u v` inner-object universe;
endpoint equality transport uses `congrArg F.obj`. No errors or warnings remain.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
