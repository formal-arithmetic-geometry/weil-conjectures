## Worker report

Repair of the independent return at immutable head 6a1fa676081a (H4/H12).
The saved packet was inspected and its initial deliver2.py --no-push passed
(commit 12e60052331), but it still contained the duplicate category identified
in the return. This repair changes the actual theorem interface and removes
that duplicate; it is not an unchanged re-push.

GroupoidCoinductionAdjunction.lean states
AlgebraicGeometry.Scheme.exists_groupoid_coinduction_adjunction, with a sorry
proof. It now imports Sheaf.AlgebraicGeometry.SchemeGroupoidModule and uses
GroupoidModule s t e i c hG and GroupoidModule.forgetToQuasiCoherent.
The duplicate GroupoidQuasiCoherentModule.lean and the new node
def-sfb-groupoid-quasi-coherent-module have been dropped from the packet.
The item cites the already landed def-sfb-scheme-groupoid-module instead.
No definition node or dependency module is delivered. The natural-language
statement and its accepted proof split are unchanged.

The @[irreducible] groupoidModulePullback wrapper is unfolded explicitly in
converting M.beta.inv to the ordinary tensor-pullback Hom type in the unit
clause. This is only definitional conversion of the given inverse, not a
new map or an arbitrary comparison. The backward transparency options permit
reduction of the existing forgetful functor and full-subcategory projections.

Sources read: Stacks groupoids.tex, Tags 03LI (definition-groupoid-module), 07TR
(lemma-construct-quasi-coherent), and 0GNF (remark-adjunction-map), including the
complete pair-groupoid/descent proof and the unit formula. Also read the source
and docstrings of every statement dependency. The latest blueprint's
sk-thm-sf-ctf-stability-direct-images.md and its proof retain the direct-image
compactification argument; this supporting Stacks prerequisite changes neither the
unit statement nor its route.

Hypothesis and clause correspondence:

- S, U, R are arbitrary Scheme.{u}. The morphisms p : U ⟶ S and q : R ⟶ S,
  together with _hs : s ≫ p = q and _ht : t ≫ p = q, put s and t over S.
  The remaining structure maps are over S by the source/target laws of hG.
- The maps s, t, e, i, c have exactly the groupoid signatures, with composition
  on pullback s t, and hG : IsGroupoid s t e i c supplies all groupoid laws.
- QCoh(U) is Mathlib's (SheafOfModules.isQuasicoherent U.ringCatSheaf).FullSubcategory.
  There is no finite-type, coherence, or finite-presentation restriction.
- The category C is precisely the landed GroupoidModule s t e i c hG. Its
  moduleObj and quasiCoherent fields give the underlying quasi-coherent module;
  beta is the t-pullback to s-pullback isomorphism. Its unit field uses
  groupoidModuleUnitLaw, expressing e*beta = 1 after the canonical comparisons.
  Its cocycle field uses groupoidModuleCocycleLaw, with fst the later arrow,
  expressing pr1*beta after pr0*beta. The comparisons are exactly the
  section-normalized tensorPullbackSectionComp and tensorPullbackSectionId.
- GroupoidModule.Hom is the subtype of underlying maps f with
  (groupoidModulePullback t).map f ≫ N.beta.hom =
  M.beta.hom ≫ (groupoidModulePullback s).map f. This is the stated
  s*f ∘ beta = gamma ∘ t*f, with the two sides of the equality exchanged.
  Identities and composition are the underlying ones.
- V is GroupoidModule.forgetToQuasiCoherent (hG := hG), which forgets descent
  and retains the existing quasi-coherence proof.
- [Flat s] [Flat t] express flatness on every stalk (Flat.iff_flat_stalkMap).
  [QuasiCompact s] [QuasiCompact t] give the affine-open quasi-compactness test;
  [QuasiSeparated s] [QuasiSeparated t] mean quasi-compact diagonals.
- G has source the full quasi-coherent subcategory and target C. The existential
  adj is the actual adjunction V ⊣ G.
- The functor equality h says G ⋙ V ⋙ inclusion = inclusion ⋙ t* ⋙ s_*.
  Equality of functors specifies the underlying objects s_*t*H and maps s_*t*h.
  Since the maps of G are morphisms in C, their equivariance is exactly the
  required naturality of the equivariant structures in H.
- For every M in C the final equality forgets adj.unit.app M and transports
  its target along h evaluated at V(M). It identifies the result with
  (tensorPullbackSectionAdjunction s).unit.app M.moduleObj followed by
  (pushforward s).map M.beta.inv, converting the latter's pullback wrappers
  definitionally. Thus the first arrow is precisely the ordinary normalized
  adjunction unit, and the second is s_*(beta inverse).

Dependency declarations used (their full signatures and docstrings were read):

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom.
- Sheaf.AlgebraicGeometry.SchemeGroupoidLaws: Scheme.IsGroupoid.
- Sheaf.AlgebraicGeometry.CoherentFiniteType (publicly imported by the landed
  category): Mathlib's SheafOfModules.IsQuasicoherent and isQuasicoherent.
  The stronger IsQuasiCoherentFiniteType predicate is not used by this item.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction (publicly imported
  by the landed category): Scheme.Modules.tensorPullbackSectionAdjunction,
  tensorPullbackSectionComp, tensorPullbackSectionId, and the publicly imported
  upstream Scheme.Modules.tensorPullback. The tensor construction and its
  uniquely section-normalized adjunction are retained.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: AlgebraicGeometry.Flat.
- Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated: QuasiSeparated.
- Sheaf.AlgebraicGeometry.SchemeGroupoidModule: Scheme.GroupoidModule,
  GroupoidModule.forgetToQuasiCoherent, groupoidModulePullback, and the category,
  Hom, unit and cocycle interfaces described above. This is the Q31 definition
  already landed on 2026-10-23; no private copy remains.
- Mathlib's pullback, pullback.fst, pullback.snd, pullback.condition and the full
  subcategory infrastructure are used through these recorded dependencies.

Advisory H9: the two non-public proof-only imports Sites.Fpqc and
WeilConjectures.AlgebraicGeometry.Descent are retained under stages/2-statements.md
section 3 rule 7 and brief-stage2 section 3: they are the modules of the recorded
proof dependencies def-weil-pbc-fpqc-covering and lem-pc-fpqc-descent. Their use is
in proof step 2, rather than in the signature. The proof dependency
lem-sfb-cartesian-groupoid-pushforward-adjunction has no usable recorded Lean
module, so no import for it is invented; its role is in proof step 4.

Edge cases checked: empty scheme/groupoid, zero module, identity groupoid,
and group scheme over a point. There is no Nonempty hypothesis. No
Noetherianity, affine or finite-presentation assumption is added. In the
identity case the groupoid unit condition forces beta to the identity under
the canonical comparisons. For a finite constant group over a point this
is functions-on-the-group coinduction with the inverse-action unit. The
arbitrary universe u covers the same scheme/module universes as the
recorded dependencies. No statement dispute or mathematical correction is needed.

Searches actually made via msearch.py (logged in searches.jsonl):

- LeanFinder, `coinduction equivariant quasi coherent modules scheme groupoid
  adjunction`: eight hits, ordinary scheme module adjunctions and representation
  coinduction. None is the scheme-groupoid theorem.
- Loogle, `IsRightAdjoint`: reported unknown identifier and no hits; this query
  was not treated as evidence of absence. The subsequent valid quoted query
  `"Groupoid", "Module"` returned zero hits.
- LeanSearch, `Category of quasi coherent equivariant modules on a scheme groupoid`:
  eight hits, IsQuasicoherent, QuasicoherentData, isQuasicoherent and Scheme.Modules;
  these give the underlying quasi-coherent category but no equivariant datum.
- Mathlib grep, `Groupoid.*Module|groupoid.*module|equivariant.*quasi`: zero hits.
  The earlier grep `coinduction|equivariant` with a Mathlib/AlgebraicGeometry
  subdirectory incorrectly repeated the Mathlib prefix; it is not used as
  evidence. The subsequent whole-Mathlib grep is the valid search above.
- Direct rg in lean/WeilConjectures and lean/Sheaf by the item id, groupoid/module,
  coinduction, equivariant/quasi-coherent, and the proposed declaration names:
  no exact theorem was found; the later landed-category check supersedes the
  earlier category-absence result. Representation, condensed coefficient
  coinduction, torsor-associated modules, and stable pointed moduli groupoids
  concern different categories.
- Whole-DAG definition-node search for groupoid/module terminology: no category
  definition was found at the original search time. That absence claim is
  superseded by def-sfb-scheme-groupoid-module, which is now used. No duplicate
  category definition is delivered.
- blueprint_refs.py searches `groupoid quasi-coherent`, `equivariant module`,
  and `groupoid module`: zero blueprint matches. The previous packet used these
  searches to support its new node; this repair removes that node entirely.

Repair search and self-check: current rg searches in lean/WeilConjectures and
lean/Sheaf for the item id, exists_groupoid_coinduction_adjunction and groupoid
coinduction found no duplicate theorem. Reading the current DAG record and
SchemeGroupoidModule.lean found the exact already landed category, its forgetful
functor, and its irreducible pullback wrapper. This supersedes the original
category-absence searches. Re-reading Stacks 03LI, 07TR and 0GNF confirms the
object laws, composition orientation, adjunction and inverse-beta unit.

Validation: the repaired theorem module compiled cleanly through scompile.py
under both sandbox and library module names (6.6 s and 19.4 s respectively),
with no errors or non-sorry warnings. There is exactly one sorry, the named
theorem proof. There are no diagnostic commands, automatic implicit binders,
new definitions, or lines over 100 characters. Comparing against the current
repository node, only lean and stmt_deps change, the latter solely by adding
the already landed def-sfb-scheme-groupoid-module. The repaired-packet dry run
passed preflight and compilation (commit 6f054c80ae3), staging only the item node,
the theorem module, and this report. No duplicate category node or module is staged.

## Second reading by Q39

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
