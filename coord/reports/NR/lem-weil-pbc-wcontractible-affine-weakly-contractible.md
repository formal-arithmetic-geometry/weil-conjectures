## Worker report

The module `Sheaf.AlgebraicGeometry.WContractibleAffineEvaluation` states
`AlgebraicGeometry.Scheme.ProEt.surjective_app_of_affine_ring_retractions`, with
its sole proof postponed by `sorry`. No definition or dependency is replaced.
The natural statement is unchanged.

Hypothesis and conclusion correspondence:

- The base scheme is `(X : Scheme.{u})`; the commutative ring is
  `(A : Type u) [CommRing A]`.
- The affine object `T = Spec A` with its structure map to X is
  `(f : Spec (CommRingCat.of A) ⟶ X) [WeaklyEtale f]`.
  `ProEt.mk f` is precisely this object of the full small site.
- Every faithfully flat weakly etale ring map out of A is quantified as
  `∀ (B : Type u) [CommRing B] (φ : A →+* B),
  φ.FaithfullyFlat → φ.WeaklyEtale → ...`.
  These are arbitrary ring maps, not only finite, finitely presented, or ind-etale maps.
- A ring retraction is `∃ r : B →+* A, r.comp φ = RingHom.id A`.
  The composite order is the one specified by the node.
- The two sheaves of sets on the full site are
  `F G : Sheaf (topology X) (Type (max (u + 1) v))`.
  They are not sheaves restricted to an affine subsite.
- A morphism is `(α : F ⟶ G)`, with `[Epi α]` expressing right cancellation
  in that category of sheaves, rather than pointwise surjectivity.
- The conclusion `Function.Surjective (α.hom.app (op (ProEt.mk f)))`
  is exactly surjectivity of F(T) → G(T).
- The size convention is explicit: schemes and rings are U-small (`u`),
  the site has object universe `u+1` and morphism universe `u`, and sets lie
  in any larger ambient universe `max (u+1) v`. The arbitrary `v` allows
  enlargement of the ambient universe; the ring-test universe is the same
  as the schemes' bound, not an independently smaller universe.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` (exposed through the site dependency).
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: imports and exposes
  `Mathlib.AlgebraicGeometry.Sites.Proetale`, whose `Scheme.ProEt`,
  `Scheme.ProEt.mk`, and `Scheme.ProEt.topology` give exactly the small site.
  Its derived-category abbreviation is unnecessary for this sets-only statement.
- `Sheaf.RingTheory.IndPrincipalZariski`: exposes the dependency's existing
  `Algebra.WeaklyEtale`; its ring-map wrapper `RingHom.WeaklyEtale` is explicitly
  imported from `WeilConjectures.RingTheory.ProEtale.WeaklyEtale`.
- `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`, the
  ring-map form of `Module.FaithfullyFlat` recorded in the dependency.
- `def-weil-size-convention` is a metatheoretic convention and has no module.

Proof-only imports retain the available DAG proof interfaces:
`Mathlib.CategoryTheory.Sites.LocallySurjective` (sheaf epimorphisms),
`Mathlib.AlgebraicGeometry.Limits` (scheme coproducts),
`Mathlib.RingTheory.Spectrum.Prime.Topology` (compactness),
`Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale` (composition/base change),
`Mathlib.AlgebraicGeometry.Morphisms.Flat`, and
`Mathlib.AlgebraicGeometry.OpenImmersion`.
The covering-section lemma has no recorded declaration yet and is only a proof
prerequisite; it is not needed to state this theorem. No wait is necessary.

Edge cases: no nonzero or nonempty assumption is made. If A is the zero ring,
Spec A is empty, and the empty covering makes sheaf values singletons, so the
conclusion is still correct. Empty covering families in the proof are retained.
The base X may also be empty. No affine, quasi-compact or separated assumption
is imposed on X. All characteristic and identity-epimorphism cases are included.
The source proof in proetale.tex, definition-w-contractible and
lemma-w-contractible-is-weakly-contractible (Tags 0981 and 098H), was read;
the four-step small-site adaptation in the node is carried in the docstring.

Searches (2026-10-15):

- `msearch.py leanfinder`: “An affine w-contractible scheme has surjective
  evaluation on epimorphisms of sheaves on the proetale site”: eight hits,
  including generic sheaf local-surjectivity and condensed-set epimorphism
  criteria, none giving the affine ring-splitting implication.
- `msearch.py loogle '"WeaklyContractible"'`: zero hits.
- `msearch.py grep 'WContractible|WeaklyContractible|weakly.contractible'`:
  zero Mathlib hits.
- `rg` with the same pattern and the item's exact id in upstream
  `WeilConjectures` and project `lean/Sheaf`: ring-theoretic
  `IsWContractibleRing` and its retraction results, plus consumers concerning
  pro-etale hypercovers, components and finite-coproduct evaluation. None states
  this full-site affine evaluation implication. In particular, the ring class
  itself is not substituted for the node's explicit retraction hypothesis.

Validation: `scompile.py NR lem-weil-pbc-wcontractible-affine-weakly-contractible`
compiled the delivered module on the server in 1.4 seconds with nice 19,
two threads, and the 60-second per-file limit. There were no errors or warnings.
All variables and universes are explicitly bound. No statement faults or disputes.

## Second reading by NR

Independently read the sandbox node and module against proetale.tex,
`definition-w-contractible` (0981), `lemma-w-contractible-proetale-cover`
(098F), and `lemma-w-contractible-is-weakly-contractible` (098H), including
both sections' introductory assumptions. Also read sites.tex,
`lemma-w-contractible` (090K), condition (2), and
`definition-w-contractible` (090L). The source's 098H is formulated on a big
site; the node explicitly takes only its forward implication on the small
site. Its proof works there: opens of a weakly etale object remain objects,
the local maps are over X, and the gluing uses covers of the same topology.
No big-site converse or size-bound cover-existence assertion is imported
into this statement.

Object/hypothesis/conclusion checklist, in node order:

1. Arbitrary base scheme X: `(X : Scheme.{u})`. Pass; no Noetherian,
   separation, quasi-compactness, or field hypothesis. Read Mathlib's
   `Scheme` structure (locally ringed space with local affine charts).
2. Full small pro-etale site, with the size convention:
   `Sheaf (topology X) ...`. Pass. Opened the dependency nodes and
   `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`; followed its public
   import to Mathlib's `Scheme.ProEt`, `ProEt.mk`, `ProEt.precoverage`, and
   `ProEt.topology`. The category is weakly etale schemes over X with all
   X-morphisms; the topology is generated by weakly etale fpqc covers.
   It is not an affine-only subsite or a Zariski topology. The derived
   category abbreviation is not used in this sets-only lemma.
3. Commutative ring A and affine site object T: `(A : Type u) [CommRing A]`,
   `(f : Spec (CommRingCat.of A) ⟶ X) [WeaklyEtale f]`, `ProEt.mk f`.
   Pass. Opened the recorded `Spec` definition and the scheme-morphism
   `WeaklyEtale` class: flat with flat diagonal. Thus T has precisely the
   required structure map, with no extra property of f.
4. Every faithfully flat weakly etale ring map out of A:
   `∀ (B : Type u) [CommRing B] (φ : A →+* B),
   φ.FaithfullyFlat → φ.WeaklyEtale → ...`. Pass. Read the faithfully-flat
   dependency record and Mathlib's `RingHom.FaithfullyFlat`: it uses B as
   an A-module via `φ.toAlgebra`. Read the ind-etale dependency record,
   its module, upstream `RingHom.WeaklyEtale`, and Mathlib's
   `Algebra.WeaklyEtale`: flatness of B and tensor multiplication. This
   uses the dependency's weakly etale clause, not the stronger ind-etale
   clause or finite presentation. There is no private replacement.
5. Existence and normalization of the retraction:
   `∃ r : B →+* A, r.comp φ = RingHom.id A`. Pass; composite A → B → A,
   with the required equality of ring maps.
6. Every two sheaves of sets on that full site:
   `(F G : Sheaf (topology X) (Type (max (u + 1) v)))`. Pass; sheaves are
   contravariant functors satisfying gluing, and the codomain includes
   arbitrary sets in the chosen larger ambient universe.
7. Every epimorphism of these sheaves: `(α : F ⟶ G) [Epi α]`. Pass;
   this is categorical right cancellation, not assumed pointwise
   surjectivity. No local lift or splitting of α is assumed.
8. Surjectivity of evaluation at T:
   `Function.Surjective (α.hom.app (op (ProEt.mk f)))`. Pass; this is
   precisely F(T) → G(T), for the same f, F, G, and α. The quantifier
   order matches the node and no additional conclusion is asserted.

Edge cases: A may be the zero ring, so T may be empty. The empty covering
forces sheaf sections there to be a singleton, giving the asserted
surjectivity. X may itself be empty. Empty index sets and zero-term
clopen covers in the proof are permitted. There is no integer parameter,
characteristic restriction, or nonzero assumption. Rings/test algebras and
schemes all use u, so the ring test is not placed in an independently
smaller universe. The site has objects in u+1 and morphisms in u; the
arbitrary ambient set universe `max (u+1) v` covers every larger choice
and permits smaller-valued sheaves by the usual lift. No equality of site
object and morphism universes is imposed.

Independent searches used different wording from the first reader:

- `msearch.py leanfinder`: "A splitting condition on faithfully flat
  algebras makes evaluation of a sheaf epimorphism surjective"; eight
  hits, including presheaf-of-modules epimorphism criteria, condensed
  local-surjectivity criteria, and flat scheme epimorphisms. None is
  this theorem about set sheaves on the small pro-etale site.
- `msearch.py loogle`: `"surjective", "Sheaf"`; twelve hits, chiefly
  presheaf module criteria and `Presheaf.IsLocallySurjective`, none exact.
- `msearch.py grep`: `retraction.*[Ss]heaf|[Ss]heaf.*retraction|[Cc]ontractible`;
  returned unrelated topological contractibility results.
- Direct `rg` in Mathlib, upstream WeilConjectures, the group's exact
  lean/WeilConjectures framework and lean/Sheaf for evaluation,
  projectivity, epimorphisms and contractibility. The upstream
  `projective_unit_of_iso` is about module sheaves over an algebraically
  closed field, not this general ring-splitting hypothesis. Opened
  upstream `RingTheory/ProEtale/WContractible.lean`: its
  `IsWContractibleRing.exists_retraction` concerns ind-etale ring maps,
  not evaluation of full-site set sheaves. No duplicate was found.

Checked H5/H6/H8/H9: no new definition, no hollow data, one theorem with
`sorry` proof only; explicit universes u v and bound variables; source and
blueprint docstrings; all four DAG proof steps appear in the theorem's
docstring. The available proof-dependency modules are imported, while
`lem-weil-pbc-wcontractible-cover-section` has no declaration yet and is
only a proof prerequisite. No new nodes or dependency modules are part of
this delivery. The node has no statement_change, and none is needed.

Mismatches found: none. Changes: appended this independent review only;
the Lean module, node statement, dependency list, and recorded signature
remain unchanged. Verified the recorded lean.statement is verbatim the
module's signature. Server compilation and delivery preflight are recorded
below.

Second-reader validation: explicit scompile.py run passed cleanly, compiling
WContractibleAffineEvaluation in 1.5 seconds (dependency overlay in 1.3 seconds),
nice 19, two threads, 60-second per-file limit. Signature and line-width
checks passed. deliver2.py --no-push printed OK: preflight and server
compilation passed, with exactly the report, item node and module staged.
