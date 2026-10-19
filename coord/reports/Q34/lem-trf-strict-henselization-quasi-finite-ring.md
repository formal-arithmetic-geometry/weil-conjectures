## Worker report

This repairs returned immutable head `97357cf7919251a1cdec0f96b06cd63e18dd1277`.
The retained packet passed the prescribed initial `deliver2.py --no-push`, but
that mechanical pass did not address the substantive review. The repair adds
module finiteness for the full strict-henselization ring map and the two
structural-map equations for the localization isomorphism, as required by H3.
It also repairs H8: a module docstring, the literal blueprint marker on the
helper, and all seven natural-language proof steps on the theorem. The module
now imports the current recorded functoriality interface and the stated proof
dependencies. Comparison with the current shared node showed only the `lean`
field differed; its statement, dependencies, and seven proof steps are retained.
No statement correction, dependency repair, or new node is needed.

The module `Sheaf.TraceFormula.StrictHenselizationQuasiFiniteRing` defines the
real structural algebra `AlgebraicGeometry.Scheme.strictHenselizationAlgebra`
from global sections of `strictHenselizationStructuralMap`, using `ΓSpecIso`.
It states `AlgebraicGeometry.Scheme.strictHenselization_quasiFinite_ring`; its
whole proof is `sorry`. Source: Stacks Project, Algebra, Tag 05WR,
`lemma-quasi-finite-strict-henselization`, read in
`literature/stacks-project/algebra.tex` at its full statement and proof.

Hypothesis and clause correspondence:

* Ring map A → B: `[CommRing A] [CommRing B] [Algebra A B]`.
  Finite type is `[Algebra.FiniteType A B]`; quasi-finiteness at the specified
  prime `q : PrimeSpectrum B` is `hq : Algebra.IsQuasiFiniteAtPrime A B q`.
  No extra finiteness, Noetherian, separability, reducedness, or domain
  hypothesis is imposed. The parenthetical finite-map case follows from the
  recorded `Algebra.finiteType_and_isQuasiFiniteAtPrime_of_finite`.
* The algebraically closed ambient field is `{Ω : Type u} [Field Ω]
  [IsAlgClosed Ω]`. The residue embeddings are the geometric morphisms
  `pbar : Spec (.of Ω) ⟶ Spec (.of A)` and
  `qbar : Spec (.of Ω) ⟶ Spec (.of B)`, by `Scheme.SpecToEquivOfField`.
  `qbar_point` sets its point equal to q. The equality `compat` identifies
  pbar with qbar followed by the given spectrum map, encoding that q lies
  over p and that the chosen residue embeddings are compatible. Thus p is
  determined by pbar rather than redundantly bound as a separate prime.
* The two strict henselizations are exactly `strictHenselizationRing pbar`
  and `strictHenselizationRing qbar`, the recorded pointed affine etale
  neighbourhood colimits. The two existential `IsLocalRing` instances
  assert locality of those rings; they are conclusions, not premises.
* The ring homomorphism φ is required to satisfy `Spec.map φ =` the
  canonical `strictHenselizationMap`, with its target transported along
  `compat`. Since Spec is faithful, this determines the canonical map.
  `IsLocalHom φ` asserts locality. The NEW conjunct
  `@Module.Finite (strictHenselizationRing pbar)
  (strictHenselizationRing qbar) _ _ φ.toAlgebra.toModule` asserts module
  finiteness of the full map, separately from residue-field finiteness.
* The induced residue map is `IsLocalRing.ResidueField.map φ`.
  `Module.Finite` for its induced module and `IsPurelyInseparable` for its
  induced algebra assert precisely the finite purely inseparable extension.
* The map `ε : TensorProduct A (strictHenselizationRing pbar) B →+* Ω`
  is specified on every pure tensor: evaluate r using
  `strictHenselizationPointEvaluation pbar`, evaluate b using qbar on
  global sections and `ΓSpecIso`, and multiply. Pure tensors generate the
  tensor product, so ε is determined. `hε` asserts that its kernel is prime.
* The ring isomorphism `e : strictHenselizationRing qbar ≃+*
  Localization.AtPrime (RingHom.ker ε)` now has BOTH structural equations.
  For each r, `e (φ r)` equals the localization image of `r ⊗ 1`.
  For each b, e of its image under `strictHenselizationStructuralMap qbar`
  on global sections equals the localization image of `1 ⊗ b`.
  Thus the inverse isomorphism is the unique localization extension of
  `r ⊗ b ↦ φ(r)·b`, not an unconstrained abstract ring equivalence.
  This expresses the canonical identification in the node.

The tensor product over A is the equivalent presentation accepted explicitly
by the returned review. It gives the same localized ring as the node's
`A_p^sh ⊗[A_p] B_q`: elements outside p are units in the source strict
henselization; elements outside q have nonzero evaluation in Ω and therefore
become units after localization at ker ε. The universal properties identify
the two presentations preserving both structural maps. This is exactly the
node's proof step 7; no source/node statement change is made.

Dependency declarations used:

* `WeilConjectures.RingTheory.QuasiFiniteAtPrime`:
  `Algebra.IsQuasiFiniteAtPrime` (recorded finite-type fibre-isolation notion).
* `Mathlib.AlgebraicGeometry.Morphisms.Finite`:
  `AlgebraicGeometry.IsFinite` and its ring-module finiteness convention;
  `IsIntegralHom` remains imported transitively with that dependency.
* `Mathlib.FieldTheory.IsAlgClosed.Basic` and
  `Mathlib.AlgebraicGeometry.ResidueField`: `IsAlgClosed` and
  `Scheme.SpecToEquivOfField`, giving geometric points and residue embeddings.
* `Sheaf.AlgebraicGeometry.StrictHenselization`: `strictHenselizationRing`,
  `strictHenselizationScheme`, and the pointed-colimit construction.
* `Mathlib.FieldTheory.PurelyInseparable.Basic`: `IsPurelyInseparable`;
  `Module.Finite` renders finiteness of the ring module and the residue module.
* Current recorded module `Sheaf.Paper.StrictHenselizationFunctoriality`:
  `AlgebraicGeometry.strictHenselizationFunctoriality`. The module also uses
  `strictHenselizationMap` and `strictHenselizationPointEvaluation` from
  `Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`, publicly imported
  through `StrictHenselizationClosedLift` (whose
  `strictHenselizationClosedLift_over` is the pointed factorization).

The theorem docstring follows every node proof step: functoriality and kernel
contractions; four-rings quasi-finiteness; the finite henselian factor;
finite purely inseparable and separably closed residue; ind-etale base change
and localization; the weakly-etale strictly-local isomorphism; structural
localization compatibility and transport of finiteness. Modules of the stated
proof dependencies are imported without `public` for future proof work.

Edge cases checked: the identity A = B; a split finite etale algebra with
several local factors (the kernel selects one factor); finite separable
extensions (strict local map can be an isomorphism); positive-characteristic
finite purely inseparable extensions (nontrivial residue extension allowed);
characteristic zero (pure inseparability forces the residue map to be an
isomorphism); and nonreduced finite fibres. In particular, residue finiteness
alone does not imply full ring finiteness: that is now a separate conjunct.
A zero ring cannot admit the specified geometric point, so this is correctly
excluded by data already in the node. The two structural equations hold also
for identity maps and nilpotents. No additional hypotheses were introduced.

The previous packet's searches are retained rather than restarting the
investigation:

* `msearch.py leanfinder`: “finite quasi-finite local ring map strict
  henselization finite local purely inseparable residue extension”; ordinary
  quasi-finite and finite-residue declarations, no comparison theorem.
* `msearch.py loogle`: `HenselianLocalRing, Module.Finite`; no hits. The
  earlier malformed/unknown-identifier queries recorded in the node were
  failed preliminary searches, not evidence of absence.
* `msearch.py grep`: `strictHenselization|Henselization|purely inseparable`
  in Mathlib; Henselian root-lifting and purely-inseparable infrastructure,
  no strict-henselization comparison.
* `rg` in `WeilConjectures/` and `lean/Sheaf/`: strict-henselization
  construction, canonical map, and closed-lift declarations, no Tag 05WR
  theorem. Repair-time `rg` on `Module.Finite`/`toAlgebra` and localization
  equivalences checked the existing module/algebra conventions.
* The current six statement-dependency node records were reread; current
  functoriality now records `Sheaf.Paper.StrictHenselizationFunctoriality`,
  so that module is imported directly. The original definition node and its
  seven-step proof are unchanged outside `lean`.

No `STATEMENT-DISPUTED` issue remains. All variables/universes are explicitly
bound (`set_option autoImplicit false`). The helper has real ring-map data,
there is one named postponed theorem, and the node's `lean.statement` is copied
verbatim from that theorem's signature. The `lean.declarations` list includes
both the helper and the theorem; the date is obtained from current UTC.

## Second reading by Q34

The dispatcher forbids starting another agent, so this is a separate self-review
pass over the final node, source, and module, not a claim of another worker's
review. The maintainer's independent review remains the external check.

The returned version was missing full ring finiteness, despite the report's
incorrect claim that finite-local had an explicit conjunct. The repaired
signature now has THREE distinct property clauses: locality of φ, finiteness
of H as an R-module via φ, and finiteness/pure inseparability of the residue
extension. I checked the `@Module.Finite` arguments: the first uses the full
rings with exactly `φ.toAlgebra.toModule`, the second uses the residue map.

The returned bare isomorphism is now constrained on the two tensor generators:
`e (φ r)` is the localized left generator and `e (B → H)(b)` is the localized
right generator. I checked its orientation H → C_n and both evaluation
formulas against source proof steps 6 and 7. These equations determine the
inverse localized tensor map and rule out an arbitrary automorphism of H.

I matched all binders against the node: finite type and quasi-finiteness at q,
algebraically closed Ω, the specified point q, and compatible geometric points.
The source point p is their forced contraction; no local-ring or residue
identification is assumed as new input. The colimits and canonical map are the
recorded objects. The equivalent tensor presentation and edge cases above
survive the new finiteness and compatibility clauses. I also checked the
module/header docstrings, literal blueprint markers, seven proof steps,
explicit universes, sorry-only proof, 100-character line bound, and verbatim
JSON signature. The statement now contains both substantive clauses requested
by the review; no other mathematical mismatch was found.

Final validation: `scompile.py Q34
lem-trf-strict-henselization-quasi-finite-ring
lean/Sheaf/TraceFormula/StrictHenselizationQuasiFiniteRing.lean` compiled the final
module cleanly in both sandbox and library-overlay passes (4.4 s and 4.8 s),
with no diagnostics. A local text/JSON self-check confirmed that only `lean`
differs from the current node, the signature matches verbatim, the sole proof
is `by sorry`, and every Lean line has at most 100 characters.
