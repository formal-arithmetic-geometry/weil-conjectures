## Worker report

The main module `Sheaf.AlgebraicGeometry.SchemeRingedEtaleReconstruction` states
`AlgebraicGeometry.Scheme.EtaleRinged.scheme_ringed_etale_reconstruction`, with
one `sorry`. No theorem is proved. Its declaration docstring contains the node's
nine-step proof, including the two open-cover gluing arguments and the uniqueness
of the glued isomorphism. The source read was etale-cohomology.tex at
lemma-etale-site-locally-ringed (04HZ), lemma-morphism-locally-ringed (04I5),
lemma-2-morphism (04IJ), lemma-faithful (04LW), and theorem-fully-faithful (04I7).

Clause-by-clause correspondence:

- The size convention is the explicit universe `u`; `Scheme.{u}` is Mathlib's
  scheme, with its actual locally ringed-space morphisms `U ⟶ V`. The full étale
  site has object universe u+1 and arrow universe u. The delivered `Site X` is
  `SmallModel.{u} X.AffineEtale`, with its induced topology. This uses the existing
  Mathlib essentially-small instance for the affine basis, rather than imposing
  SmallCategory on the full étale site or identifying distinct universes. The
  explicit `setEquivalence X` identifies the full étale topos with this model.
- Structure sheaf: `commRing X` restricts the existing
  `X.etaleStructurePresheaf` and its existing sheaf proof. `ring X` forgets only
  commutativity. Its section rings remain the actual Γ(T, O_T), with no lift,
  choice of ring, or substitution of a constant coefficient sheaf.
- Ringed-topos morphisms are exactly the recorded
  `CategoryTheory.RingedToposMorphism`, abbreviated `Morphism U V`. It has the
  set-sheaf geometric adjunction, finite-limit preservation, generalized-element
  ring identities, and the induced additive module direct image. No site-induced
  hypothesis is put on an arbitrary morphism `g`.
- “Locally a or 1-a invertible” and “equalizer of 0,1 initial” are precisely the
  existing `CategoryTheory.IsLocallyRingedTopos`; its second condition says that
  0=1 implies that the empty sieve covers. The first conjunct quantifies over
  every scheme X and asserts this for `ring X`.
- “Local” is the existing `RingedToposMorphism.IsLocal`, the pullback square of
  unit inclusions and structural ring maps. The second conjunct quantifies over
  every U,V and a and supplies h with `Induces h a ∧ h.IsLocal`.
- The canonical induced morphism is characterized, rather than chosen from an
  unproved existence assertion: `Induces h a` supplies a natural isomorphism on
  ALL étale representables to the actual base-changed representables; for every
  chart T and EVERY regular function s its equation identifies the structural
  map with evaluation of the pullback along `pullback.fst T.hom a`. These
  representables generate the topos; hence the normalization specifies exactly
  the scheme-induced ringed morphism up to ring-compatible isomorphism. It does
  not replace the canonical construction by an arbitrary map. All the defining
  data (restriction, functions, evaluations, base-change functor) are real terms.
- For every arbitrary local `g`, the third conjunct is `∃! a : U ⟶ V`, with
  predicate `∃ h, Induces h a ∧ Nonempty (TwoIso g h)`. This is exactly existence
  and uniqueness of the underlying scheme morphism, allowing the unavoidable
  isomorphism of induced geometric morphisms. In particular it does not ask for
  equality of arbitrarily chosen adjunction or module-functor records.
- `TwoIso g h` consists of `iso : g.inverse ≅ h.inverse` and the equality
  `iso.hom.app (ringSheafUnderlying (ring V)) ≫ h.ringMap = g.ringMap`. Thus it
  uses precisely a natural isomorphism commuting with the structural maps.
- The fourth conjunct quantifies over every a, every induced h and EVERY natural
  endomorphism t of its inverse image. The sole premise is the same ring-map
  compatibility equation; the conclusion is `t = 𝟙 h.inverse`. No invertibility
  assumption is inserted for the endomorphism.
- The final conjunct is `Subsingleton (TwoIso g h)` for every g and induced h.
  This says any two such isomorphisms coincide, including their compatibility
  proofs by proof irrelevance. It does not unnecessarily assert that an
  isomorphism exists for arbitrary g.
- There are no separation, quasi-compactness, quasi-separatedness, affineness,
  finite-type or nonemptiness assumptions anywhere in the main signature.

Dependencies read and used: Mathlib.AlgebraicGeometry.Scheme (`Scheme`,
`Scheme.Hom`), Mathlib.AlgebraicGeometry.Sites.Etale (`Scheme.Etale`,
`Scheme.smallEtaleTopology`), Sheaf.CategoryTheory.RingedToposMorphism
(`CategoryTheory.RingedToposMorphism`), and the landed definition
Sheaf.CategoryTheory.LocallyRingedTopos (`ringSheafUnderlying`,
`IsLocallyRingedTopos`, `RingedToposMorphism.IsLocal`). The latter node is added
to stmt_deps, alongside the new presentation definition. Mathlib's
`Scheme.AffineEtale`, `AffineEtale.Spec`, `AffineEtale.topology`,
`AffineEtale.sheafEquiv`, `SmallModel`, `equivSmallModel`, and
`Equivalence.sheafCongr` provide the actual basis transport.
WeilConjectures.AlgebraicGeometry.Sites.Gm supplies
`Scheme.etaleStructurePresheaf` and `Scheme.isSheaf_etaleStructurePresheaf`.
Their full definitions and docstrings were read, including the formula for
`etaleStructurePresheafToPullback`.

All recorded proof modules are imported as plain imports, including
EtaleInverseImageAlgebraicStructures, EtaleSetInverseImageStalkGerm,
StrictHenselizationFunctoriality, InverseImageRepresentable,
CoveringRepresentableCoequalizer, SmallEtaleRepresentablePresheafSheaf,
LocalizedSheavesOverRepresentable, EtaleOver, RingedToposSliceFunctoriality,
EtaleSubsheafFinalOpen, and Mathlib's adjunction/point/gluing/balanced interfaces.
The coordinate-monomorphism and affine-solution-comparison proof nodes have no
Lean records yet, so there are no modules to import for them; the proof docstring
names them. They are proof prerequisites, not needed for this signature.

Edge cases checked before writing: empty schemes have the degenerate sheaf topos,
and the empty-cover clause, not a sectionwise nonzero requirement, retains them.
Every local ring condition is checked after covers, not by falsely making global
sections local rings. Zero rings occur at empty charts. Identity and arbitrary
scheme maps have the same representable normalization. No affine intersections,
finite covers, rational points or separably closed-field choices occur in the
signature. Noninvertible natural endomorphisms are included. The possibly empty
type of two-isomorphisms is permitted by Subsingleton.

Searches actually run (the sandbox searches.jsonl contains the wrapper log):

- leanfinder: “A morphism of locally ringed small etale topoi of schemes comes
  from a unique scheme morphism and has no nontrivial ring compatible natural
  endomorphism” returned 8 hits, mainly Scheme.Etale.forgetFullyFaithful and
  formal unramifiedness; none is the ringed-topos reconstruction theorem.
- leanfinder: “fully faithful reconstruction schemes morphisms locally ringed
  etale topoi” returned 8 hits, including fullyFaithfulForgetToLocallyRingedSpace
  and Spec.fullyFaithful. Those concern spaces or affine spectra, not étale topoi.
- loogle: `AlgebraicGeometry.Scheme, CategoryTheory.Sheaf` returned 12 hits,
  including AffineEtale.sheafEquiv and Scheme.Hom.toRingCatSheafHom. The comparison
  is reused; neither is the requested theorem.
- msearch grep: `LocallyRingedTopos|ringedEtale|etaleStructureSheaf` returned zero
  Mathlib hits. Project rg found the existing LocallyRingedTopos module, reused.
- leansearch: “small affine etale site structure sheaf schemes morphism ringed
  topos canonical direct image” returned 8 generic hits, including
  smallEtaleTopology and Scheme.Hom.appTop, no specialized presentation.
- leanfinder: “small skeleton affine etale site structure sheaf normalized ringed
  topos morphism by functions” returned 8 generic scheme/étale hits, no exact
  definition. msearch grep `SmallModel.*AffineEtale|schemeEtaleRinged|SchemeRingedEtale`
  returned zero Mathlib hits.
- Project rg in both WeilConjectures and Sheaf for the item id, ringed étale
  reconstruction, and the normalized new names found no existing theorem or
  normalized presentation. It found the actual structure presheaf in Sites.Gm,
  existing regular-functions module rings in SchemeZariskiEtaleQuasiCoherentEquivalence,
  and local SmallModel constructions in EtaleSmallGenerator. Those use identical
  generic components but do not publicly supply the new normalized ringed interface.
  The algebraic-space small ringed model is for a different existing site and
  does not define the scheme representable normalization.
- DAG search for the small affine model found def-sc-etale-small-generator, which
  defines an abelian generator (its SmallModel and topology are function-local),
  not this ringed presentation. `tools/blueprint_refs.py search 'small affine etale
  ringed presentation'` returned 0 blueprint nodes. The ancestor command reports
  the existing parent's blueprint.from.node = None; the new node retains that
  lineage and the whole inherited via, prefixed with the item.

No statement correction or disputed statement is needed. The natural-language
statement is unchanged. The only changes to the existing item are its Lean
record and two added statement dependencies.

## New nodes

`def-sfb-scheme-etale-ringed-presentation` records the concrete small affine
presentation, its actual restricted regular-functions sheaf, the normalization
`Induces`, and the structural-map-compatible `TwoIso`. Its module is
`Sheaf.AlgebraicGeometry.SchemeEtaleRingedPresentation`. The primary declaration
is `AlgebraicGeometry.Scheme.EtaleRinged.Induces`; every helper is listed in
lean.declarations. Sources are Tags 04HZ, 04I5, 04LW and the dense-subsite
comparison (03A0). This is a definition node only: all data are real constructions,
with no postponed theorem or hidden sorry. In particular setEquivalence is the
composition of the existing affine comparison and the SmallModel site equivalence.
The three logged search kinds and DAG/blueprint searches above found no existing
node supplying this interface. The generic site, basis, structure presheaf,
restriction and ringed morphism notions are all reused.

## Validation

Both modules compiled individually through scompile.py against the live published
library. The helper has no warnings or sorry; the main module has only the
expected declaration-uses-sorry warning. All variables and universes are explicit,
with autoImplicit false. No direct Git command, local Lake compile, library edit,
or global build was used.

Source-reference check: the tag database identifies the comparison theorem as
03A0 (sites.tex, lemma-equivalence), affine étale refinement as 0218
(topologies.tex, lemma-etale-affine), and ringed two-morphisms as 04IC
(sites-modules.tex, definition-2-morphism-ringed-topoi). Those passages were read;
the helper source comments and new node use these verified tags.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
