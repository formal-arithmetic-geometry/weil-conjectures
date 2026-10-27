## Worker report

The delivery states `AlgebraicGeometry.relative_quasiAffine_group_envelope` in
`Sheaf.AlgebraicGeometry.RelativeQuasiAffineGroupEnvelope`. Its sole proof is `sorry`.
No definition, dependency repair, new node or statement correction is needed.
Only the item's `lean` field changes. The file compiled through the prescribed
`scompile.py Q18 lem-sfb-relative-quasiaffine-group-envelope <file>` on 2026-10-24:
sandbox check 20.3 seconds and library-name check 12.3 seconds, both clean.

Hypothesis and conclusion correspondence:

| Node text | Lean rendering |
| --- | --- |
| Noetherian integrally closed domain, dimension at most one; fields allowed | `(B : Type u) [CommRing B] [IsDedekindDomain B]`; Mathlib's class extends `IsDomain` and `IsDedekindRing`, exactly these conditions. It does not demand dimension exactly one. |
| K is the fraction field | `(K : Type u) [Field K] [Algebra B K] [IsFractionRing B K]`; any chosen fraction field, rather than a distinguished implementation. |
| S = Spec B | Each object is in `Over (Spec (.of B))`. |
| G and J are S-group schemes with all group diagrams | `[GrpObj G] [GrpObj J]`; the internal group-object class includes multiplication, identity, inverse and all their diagrams. It does not impose commutativity. |
| G and J flat | `[Flat G.hom] [Flat J.hom]`. |
| G and J separated | `[IsSeparated G.hom] [IsSeparated J.hom]`; the class asserts closed diagonal. |
| G and J finite type | `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` and the identical pair for J. |
| f is an S-group homomorphism | `(f : G ⟶ J) [IsMonHom f]`; the over-category ensures the base diagram. Group inverses are preserved automatically by a monoid homomorphism of group objects. |
| f quasi-affine | `[IsQuasiAffineHom f.left]`, the recorded upstream class, requiring every affine-open preimage to be quasi-affine. |
| A = f_* O_G with its induced O_J-algebra structure | `Under.mk ⟨f.left.c⟩` with explicit source and pushforward target sheaf types; its sections are definitionally sections on the inverse image. |
| A quasi-coherent | The first conjunct is `(Scheme.CommAlgebraSheaf.toModule (...)).IsQuasicoherent`; no finite-type module condition is imposed. |
| q:H = Spec_J A → J | Existential H, q, `IsAffineHom q.left`, and the algebra isomorphism `a : A ≅ q_* O_H`, followed by its isomorphic affine-chart condition. This is exactly the relative-spectrum interface in the dependency, not an arbitrary affine factorization. |
| Chart q inverse image W = Spec Gamma(f inverse image W,O) | `IsIso ((q.left ⁻¹ᵁ W).toSpecΓ ≫ Spec.map (a.hom.right.hom.app (op W)))` for every affine open W. `Opens.toSpecΓ` includes the canonical top-section identification for the open subscheme. |
| j canonical, identity on the ring on each chart | The following equality identifies the restriction of j followed by this very chart with `(f.left ⁻¹ᵁ W).toSpecΓ`. Under the Gamma--Spec adjunction this is the identity ring map, not a freely chosen map. |
| H admits an S-group structure | The existential `(_ : GrpObj H)` is attached to that same H; it is available to the following homomorphism clauses. |
| j and q homomorphisms | `IsMonHom j ∧ IsMonHom q`. |
| qj = f | Existential proof `hc : j.left ≫ q.left = f.left`. Faithfulness of the over-category forgetful functor makes this exactly equality of S-morphisms too. |
| q affine | `IsAffineHom q.left`. |
| j quasi-compact open immersion | `IsOpenImmersion j.left ∧ QuasiCompact j.left`. |
| G_K,H_K and j_K are base changes along Spec K → Spec B | `Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B K)))`, on objects and on j. This is precisely the dependency's prescribed scheme/morphism base-change functor. |
| The canonical O_(H_K) → (j_K)_* O_(G_K) is an isomorphism | The final `IsIso (((Over.pullback ...).map j).left.c)`. Scheme.Hom.c is exactly the canonical structure-presheaf homomorphism, not an existential comparison. An isomorphism of the underlying presheaf morphism is equivalent to an isomorphism of the sheaf morphism, since both are sheaves and the sheaf category is a full subcategory. |
| No finite generation for A(W), no finite type for H | Neither occurs in the conclusion. In particular the finite-type hypotheses only involve G and J. |

The existential realization is the way the already recorded relative-spectrum dependency
presents its canonical construction. Its isomorphic affine charts and the specified
canonical j identify the construction up to the unique compatible isomorphism; no
noncanonical object is selected in a definition, and no `Nonempty` choice constructs data.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, with
  `Flat.iff_flat_stalkMap` confirming the node's local-ring definition.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`: `IsQuasiAffineHom`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes
  `SheafOfModules.IsQuasicoherent`; its additional finite-type conjunction is deliberately
  not used for the quasi-coherent algebra clause.
- `WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`:
  `affine_morphism_relative_spec`, especially the affine chart characterization.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `ΓSpec.adjunction`,
  `Scheme.Opens.toSpecΓ`, underlying the canonical-map chart identity.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`:
  its recorded scheme/morphism base-change interface is `Over.pullback` (not
  `Scheme.Modules.moduleBaseChange`, which is only the module clause of that node).

Additional existing notions are `GrpObj`, `IsMonHom` from Mathlib's internal group
objects, `IsSeparated` from its closed-diagonal definition, `IsDedekindDomain` and
`IsFractionRing`. All binders and universe `u` are explicit; auto implicits are disabled.

The declared proof-dependency modules are imported without `public`: the qcqs
relative-affinization and canonical-chart lemmas, flat invertible sections,
EulerChar (the recorded `lem-pc-flat-base-change-cohom` module), torsion-free flatness,
localization flatness, flat ring-map composition, and scheme gluing. Dependencies
with no Lean record or Mathlib match (`lem-sfb-qcqs-functions-local-comparison`) are
not needed to type this statement and have no module to import. The inherited
flat-base-change node's EulerChar declaration is a specialized consequence rather
than the full general degree-zero comparison needed by this proof plan; this does
not change the statement or create a new hypothesis. Its eventual stage-3 proof
will require the general degree-zero comparison specified by that DAG proof.

Edge cases checked before writing: fields satisfy dimension at most one, so their
generic comparison is retained. The zero ring is excluded by the domain hypothesis,
as in the node. Empty affine opens give zero section rings and empty spectral charts;
no nonempty-open assumption is present. Group identity sections preclude an empty
G or J over nonempty Spec B. Nonreduced and disconnected groups, positive
characteristic and noncommutative groups are retained. The envelope need not be
finite type, so its arbitrary section algebras are allowed. No extra universe of test
objects occurs: schemes, B and any chosen fraction field K live in one arbitrary
universe, as in the published scheme library.

Searches (the wrapper also recorded exact outputs in sandbox `searches.jsonl`):

- LeanFinder, query: “The relative spectrum of the direct image of the structure
  sheaf of a quasi affine homomorphism of flat group schemes over a Dedekind domain
  admits a group scheme structure”. Eight hits, including
  `Scheme.isPullback_toSpecΓ_toSpecΓ`, `specTargetImage`, `AffineSpace`, and flat affine
  section-map lemmas. None extends group operations to this relative envelope.
- Loogle, query `IsQuasiAffineHom, GrpObj`: zero hits; the service does not know
  upstream `IsQuasiAffineHom`.
- LeanSearch, query `quasi-affine flat group scheme relative spectrum of direct image
  structure sheaf group envelope`: eight hits concerning ordinary quasi-affine
  schemes and affine maps, no matching group-envelope assertion.
- Wrapper Mathlib grep, regex `relative.*affini|quasi.*affine.*group|group.*envelope`,
  directory `AlgebraicGeometry`: zero hits.
- `rg` on both published roots for the same concept and the node id found the
  qcqs relative-affinization construction and compatible charts, but no group-envelope
  statement. Read both and the quasi-affine relative-spectrum embedding module;
  those supply the construction or embedding, not the extended group operations
  and generic canonical sheaf comparison. No duplicate notion is introduced.

Source check: read local Stacks `morphisms.tex`, lemma-characterize-quasi-affine
(Tag 01SM), especially (4); `constructions.tex`, lemma-canonical-morphism (Tag 01LY);
`coherent.tex`, lemma-flat-base-change-cohomology (Tag 02KH); and `more-algebra.tex`,
lemma-dedekind-torsion-free-flat (Tag 0AUW). The statement and docstring expressly
distinguish the agent-written group-extension argument from what 01SM itself states.
No STATEMENT-DISPUTED issue or source-based node correction was found.

## Second reading by Q18

The dispatcher explicitly prohibits starting another agent and says the maintainer
will independently review the delivery. This section therefore records a second
self-audit, not a claim that a separate worker reviewed it. Reopened the node and
Lean signature side by side: all hypotheses and clauses are paired in the table
above. In particular, checked that the same `a` determines both the isomorphic chart
and the canonical j, that `GrpObj H` is bound before both `IsMonHom` clauses, and
that the last map is the structure map of the generic base change of this same j.
Checked that `IsDedekindDomain` permits fields and that no affine, reduced, smooth,
commutative or finite-type assumption on H slipped into the binders. No mismatch
was found and no statement correction was made. The authoritative independent
reading remains the maintainer's delivery review, as the task brief specifies.
