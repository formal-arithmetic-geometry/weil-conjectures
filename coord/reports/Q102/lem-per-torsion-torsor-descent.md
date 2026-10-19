## Worker report

The module `Sheaf.AlgebraicGeometry.TorsionTorsorDescent` states
`AlgebraicGeometry.Scheme.isIndFiniteEtaleSheaf_of_free_torsion_action`, with `sorry`
as its entire proof. It introduces no definitions and changes only the item's `lean` record.
Source checked directly: ILO, Travaux de Gabber, Exposé XVII, Lemma 7.2.6,
printed pp. 302–303 / PDF pp. 308–309, read with pdftotext. The node agrees with
that lemma. The docstring carries all five proof steps from the node.

Clause-by-clause rendering:

- A Noetherian scheme: `X : Scheme.{u}`, `[IsLocallyNoetherian X]`,
  `[CompactSpace X]`. These are exactly the two components of Mathlib's
  `AlgebraicGeometry.IsNoetherian`; no connectedness or separatedness is assumed.
- Its small étale site: every sheaf has topology `X.smallEtaleTopology`, whose
  objects are `X.Etale` and whose arrows are all étale X-morphisms.
- An abelian sheaf G: `G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- A sheaf of sets T: `T : Sheaf X.smallEtaleTopology (Type (u + 1))`.
- A G-action: the family `vadd U` together with `hzero`, `hadd`, and `hnat`
  explicitly gives identity, addition compatibility, and compatibility with all
  restriction maps. This is the sectionwise expansion of a sheaf action, rather
  than a new private definition. The ordinary additive group operations are
  those of G's section groups.
- Freeness: `hfree` requires `Function.Injective (vadd U · t)` at every section t.
  This is precisely trivial stabilizers, equivalently that the action-relation
  map G × T → T × T is mono. No transitivity or local nonemptiness is required.
- Quotient sheaf T/G: `Y` is a set sheaf and `q : T ⟶ Y`; `hqinvariant` says q
  is invariant and `hquotient` is the exact categorical quotient universal
  property: every invariant sheaf morphism `f : T ⟶ E` factors through q in a
  unique way. This is the coequalizer of action and projection, stated by its
  universal property in the ambient sheaf category. The componentwise invariance
  is equality of sheaf morphisms because vadd is natural. Thus q is pinned to
  the quotient, not an arbitrary map, a chosen torsor, or a presheaf orbit set.
  Conversely the canonical sheaf quotient always has precisely these properties;
  changing its representative changes nothing because quotients are uniquely
  isomorphic and the local-system predicate is invariant under isomorphism.
- G is a local system: `hG` applies the recorded `IsIndFiniteEtaleSheaf` to
  `(sheafCompose ... (CategoryTheory.forget AddCommGrpCat)).obj G`. This is the
  underlying set sheaf, not a finite or finitely generated abelian sheaf.
- Torsion: `htorsion` quantifies over every `Ω : Type u` with `[Field Ω]` and
  `[IsAlgClosed Ω]`, every `x : Spec (.of Ω) ⟶ X`, and every
  `g : (pointedEtaleStalk G x : AddCommGrpCat.{u + 1})`. It asks for
  `∃ n : ℕ, 0 < n ∧ n • g = 0`. The existential is inside the germ quantifier;
  there is no uniform annihilator. The stalk is the recorded pointed-neighbourhood
  colimit of abelian groups, retaining its additive structure. Its required
  colimit instance is synthesized, not assumed as an additional hypothesis.
- T/G is a local system: `hY : IsIndFiniteEtaleSheaf Y`.
- Conclusion: exactly `IsIndFiniteEtaleSheaf T`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `Scheme.smallEtaleTopology`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit` and colimit universal
  property; `Limits.Cones` / `Limits.IsLimit`: `Cocone`, `IsColimit`;
  `Mathlib.CategoryTheory.Filtered.Basic`: `IsFiltered`. These occur in the
  existing ind-finite predicate, which is imported and not redefined.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the geometric-point
  presentation is the recorded inline `Ω`, `Field`, `IsAlgClosed`, `Spec Ω ⟶ X`.
  `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField` was also
  read: this is the ordinary geometric-point interpretation.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: `AlgebraicGeometry.pointedEtaleStalk`
  and `pointedEtaleStalkDiagram`, read in full. This is exactly the recorded stalk.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: read its full sheaf predicates
  and coefficient conventions. We use its ambient sheaf categories; its locally
  constant predicate is not substituted for the node's ind-finite predicate.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Sheaf.AlgebraicGeometry.IndFiniteEtaleLocalSystem`:
  `Scheme.IsIndFiniteEtaleSheaf`, read in full along with its docstring. It uses
  an arbitrary small filtered diagram of finite étale representables and an
  actual colimit cocone, including an isomorphism to the given sheaf.

The stated proof dependencies are imported without `public`: upstream Torsor,
HenselianFiniteEtale, higher-direct-image FreeSheaf, InverseImageStalkGerm;
side EtaleContractedProductExists and EtaleTorsorH1Functoriality; Mathlib finite
and finite-type morphisms. No duplicate definition of torsor or action is added.
The two proof dependencies `lem-per-set-local-system-calculus` and
`lem-per-torsion-finite-subsystem` have no recorded Lean statements in the read
DAG, so no unavailable modules are imported. They are proof-only dependencies,
not prerequisites for typing this statement. Their exact uses remain in the
proof docstring for stage 3 and later import bookkeeping.

Edge cases checked mathematically before drafting:

- Empty X is allowed, with all sheaf and germ conditions interpreted on its site.
- Empty quotient: no nonemptiness is imposed on Y or T; the quotient universal
  property forces T empty when Y is initial.
- G = 0: the action is trivial and free; its quotient is isomorphic to T.
- The terminal quotient gives the torsor case; arbitrary quotient is retained.
- Finite constant torsion groups and an infinite direct sum of Z/2 are allowed.
  Neither finite stalks nor a globally bounded exponent is imposed.
- Non-torsion Z is excluded by the genuine germwise torsion hypothesis, as
  required by ILO XVII Exercise 7.2.7. The witness n = 0 is explicitly excluded.
- Site objects remain in universe u+1 and arrows in u. Set/abelian values are in
  u+1 consistently with the existing local-system and étale-sheaf interfaces.

Searches made (wrapper records are also in the sandbox searches.jsonl):

- msearch LeanFinder: "a torsion abelian local system acts freely on a sheaf whose
  quotient is ind finite etale then the sheaf is ind finite etale"; 8 hits,
  principally SheafOfModules.IsFiniteType / IsFinitePresentation, no match.
- msearch Loogle: `CategoryTheory.Sheaf, AddAction`; zero hits.
- msearch LeanSearch: "free action of torsion abelian local system sheaf quotient
  local system"; 8 ordinary group-action/free-group/topological quotient hits,
  no sheaf local-system descent statement.
- msearch grep: `torsion.*torsor|torsor.*torsion|Sheaf.*Action|Action.*Sheaf`;
  13 unrelated Mathlib fraction and stalk hits, no match.
- rg of upstream WeilConjectures and side lean/Sheaf for torsion/torsor,
  IsIndFiniteEtale, and free actions: found the existing ind-finite definition,
  the upstream simply-transitive Torsor structure, scheme-level finite actions,
  and the downstream TorsionLocalSystemMonodromy consumer. None states this lemma.
- rg of the upstream source for the exact item id: no match.
- DAG search of definition nodes in this chapter for free actions and quotient
  sheaves found scheme/log quotients, not a competing sheaf statement. No new
  notion is introduced: action and quotient conditions are fully expanded in
  the signature using ordinary maps, operations, and the universal property.

Validation: scompile.py compiled both sandbox and final module path cleanly
(4.5 s and 3.9 s), with no errors or unexpected warnings. An initial elaboration
failure was repaired by qualifying `CategoryTheory.forget` against Scheme.forget
and explicitly typing the abelian stalk before coercing it to its carrier.
No statement fault, correction, or STATEMENT-DISPUTED remains.

## Second reading by Q102

Author's separate rereading, not an independent agent review (the dispatcher
explicitly forbids starting other agents). The maintainer's delivery review is
independent. Reopened the node and final signature and checked each clause:
Noetherian = locally Noetherian plus compact; the same small étale site; G abelian;
T a set sheaf; a natural action with zero/add laws; free action = orbit-map
injectivity; quotient = invariance plus unique factorization against every set
sheaf; local systems = the recorded ind-finite predicate for G and Y and the
same predicate for T in the conclusion; torsion = all geometric germs with
positive witness depending on the germ. No quotient finiteness, transitivity,
connectedness, chosen point, local section, uniform exponent, or nonemptiness
has been introduced. The naturality quantifies over all opposite-site arrows.
The universal property is at the category of sheaves, and uses the actual q.
The proof docstring matches the node's five stages. No mismatch found and no
node statement change required. The only compilation repairs were name
qualification and the abelian-stalk carrier annotation, which preserve meaning.
