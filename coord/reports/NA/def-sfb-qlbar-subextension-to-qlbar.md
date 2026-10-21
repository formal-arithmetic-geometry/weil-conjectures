## Worker report

This delivery binds the node to the exact existing construction
`Profinite.padicSubfieldRingObjToPadicAlgCl` in
`WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`
(lines 128–131). No module or duplicate definition is delivered. The node is unchanged
outside `lean`; no new nodes, dependency repairs, statement corrections, or disputes occur.

Source read: the full current blueprint statement and proof at
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-prop-sfb-qlbar-colimit-point/def-sfb-qlbar-subextension-to-qlbar.md`
and the node's two proof steps. Its definition agrees with the existing source module's
inclusion construction and compatibility lemma, rather than with all continuous maps
into the topological algebraic closure.

The clause-by-clause comparison is as follows.

- The prime ℓ is the module's explicit `(ℓ : ℕ) [Fact ℓ.Prime]` section binder.
  The algebraic closure is `PadicAlgCl ℓ` with its extending norm topology.
- A finite subextension E is `(E : PadicAlgCl.FiniteIntermediateField ℓ)`.
  This is exactly `{E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) //
  FiniteDimensional ℚ_[ℓ] E}`. No extra property of E is assumed.
- The source condensed ring is `continuousMapRingSheaf.{u} E`, definitionally
  `padicSubfieldCondensedRing.{u} ℓ E`, the recorded dependency's construction.
  The topology is the restricted topology of the intermediate field, agreeing with
  `PadicAlgCl.normedFieldOfAlgebra ℓ E` used by that dependency.
- The target is `padicAlgClCondensedRing ℓ`, precisely the dependency's ring of
  finite-subextension-valued continuous maps. It is not the larger continuous-map
  condensed ring of the topological algebraic closure.
- On a profinite S the source is `ULift C(S, E)` and the target is
  `ULift (PadicAlgCl.finiteIntermediateFieldValued ℓ S)`. The universe lift changes
  only the size convention for section types.
- The exact formula a ↦ inclusion ∘ a is the component at S of
  `padicSubfieldToPadicAlgClRingPresheaf` (lines 111–119):
  `(algebraMap E (PadicAlgCl ℓ)).compLeftContinuous S.unop continuous_subtype_val`.
  Its `codRestrict` uses the witness `⟨E.1, E.2, fun x ↦ (a x).2⟩`, so its values
  belong to the specified finite subextension E. Naturality is definitional.
- `padicSubfieldCondensedRingToPadicAlgCl` (lines 121–123) is the same map packaged
  as a morphism of sheaves of unital rings; pointwise operations are preserved by
  the `RingHom` component.
- The phrase “viewed as a morphism of underlying ring objects” is exactly
  `padicSubfieldRingObjToPadicAlgCl`: it applies
  `(sheafCompose (coherentTopology Profinite.{u})
  (forget₂ RingCat.{u + 1} Ab.{u + 1})).map` to that ring-sheaf morphism.
  The instance at lines 133–136 supplies `IsMonHom` for the actual ring-object
  structures from the recorded RingPresheaf dependency. Both endpoints are
  commutative by the existing ContinuousMap and EllAdic instances.
- For E ⊆ F, `(h : E ≤ F)` and
  `padicSubfieldRingObjMap_comp_toPadicAlgCl ℓ h` (lines 141–146) state
  `padicSubfieldRingObjMap ℓ h ≫ padicSubfieldRingObjToPadicAlgCl ℓ F =
  padicSubfieldRingObjToPadicAlgCl ℓ E`, exactly j_F ∘ ι_E,F = j_E.
  The transition map is the dependency's recorded declaration, not another map.

Dependency declarations were read with their docstrings and full section signatures:

- `def-sfb-padic-subfield-condensed-ring`:
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
  `Profinite.padicSubfieldCondensedRing` (lines 101–109).
- `sk-def-sfb-qlbar-condensed`: the same EllAdic module,
  `Profinite.padicAlgClCondensedRing`, `padicAlgClRingObj`,
  `padicAlgClSubfunctor`, and `padicAlgClRingPresheaf` (lines 161–251).
- `sk-def-sfb-ring-object`:
  `WeilConjectures.CategoryTheory.RingObjects.RingPresheaf`,
  `CategoryTheory.Functor.monObjCompForget₂` and especially clause 3's
  `CategoryTheory.Sheaf.monObj_sheafCompose_obj` and
  `CategoryTheory.Sheaf.isMonHom_sheafCompose_map` (lines 166–170, 199–201).
- `def-sfb-qlbar-subextension-map`: the FiniteSubextension module,
  `Profinite.padicSubfieldRingObjMap`, its condensed-ring counterpart, and strict
  identity/composition lemmas (lines 79–102).
- Proof-only dependency `def-sfb-continuous-map-condensed-ring`:
  `Sheaf.Topology.ContinuousMapCondensedRing`,
  `Profinite.continuousMapRingSheafOfUniverse`; its coefficient-universe-zero
  specialization is the upstream `continuousMapRingSheaf` used here. The existing
  module imports the upstream construction and RingPresheaf construction already;
  no import or module is added by this attachment.

Edge cases: S is any `Profinite.{u}` with no inhabitance assumption, including the
empty profinite set. The formula is valid as a function also in the empty case;
its finite-image witness remains E. For E = F compatibility includes the identity
transition. E = the bottom intermediate field gives the base-field inclusion.
Zero, one, sums and products are handled by a genuine unital ring homomorphism.
All primes are allowed, including 2; there is no characteristic exclusion. The
profinite universe u is arbitrary and never equated with a coefficient universe.
The field model is precisely a subfield of the fixed algebraic closure, so it
introduces no finiteness or universe restriction beyond the node's finite
subextension hypothesis.

Searches actually run on 2026-10-21:

- `msearch.py ... leanfinder` with query “morphism from condensed ring of finite
  p-adic subextension into finite-subextension-valued algebraic closure condensed
  ring”: eight hits, including `PadicAlgCl`, `PadicAlgCl.coe_eq`, and ordinary
  algebraic-closure facts; no condensed-ring morphism.
- `msearch.py ... loogle 'RingHom.compLeftContinuous'`: two hits,
  `RingHom.compLeftContinuous` and its application lemma in
  `Mathlib.Topology.ContinuousMap.Algebra`. These give the sectionwise operation,
  not the whole condensed inclusion.
- `msearch.py ... grep 'padicSubfieldRingObjToPadicAlgCl|CondensedRing'`:
  successful Mathlib search, zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `padicSubfieldRingObjToPadicAlgCl|padicSubfield.*PadicAlgCl|subextension-to-qlbar`:
  the exact definitions and compatibility lemma are in the upstream
  FiniteSubextension module; many Sheaf consumers already use them.
- `grep -rn 'def-sfb-qlbar-subextension-to-qlbar' lean/WeilConjectures`:
  no node-id comment match; name/concept search above finds the exact construction.
- `rg` for the main inclusion and compatibility names in
  `dag/lean_names_upstream.json`: no hits. Direct source reading supersedes this
  older index.

Validation: the sandbox-only `scratchpad/ExistingConsumer.lean` is checked using
`scompile.py NA def-sfb-qlbar-subextension-to-qlbar`. It validates the exact recorded
source and target, the sectionwise formula and its image in E, the `IsMonHom`
instance, compatibility for arbitrary E ≤ F, its identity case and the bottom
intermediate field. The first probe needed `noncomputable section` for its
map-valued examples; this affects only the probe, not any declaration being attached.
The final clean run and the delivery wrapper's declaration checks are recorded below.

Additional search: `msearch.py ... leansearch` with query “postcomposition with
inclusion of finite p-adic subextension into algebraic closure defines morphism of
condensed rings”: eight hits, including `PadicAlgCl`, `Subfield.subtype`, and ordinary
p-adic embeddings, with no matching condensed-ring morphism.

The final server consumer compiled cleanly with no errors or warnings (sandbox
28.6 seconds; library-context check 24.0 seconds). The consumer is scratch material
only and is not included in the delivery.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
