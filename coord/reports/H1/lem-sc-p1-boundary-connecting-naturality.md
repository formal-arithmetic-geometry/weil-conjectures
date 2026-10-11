## Worker report

The module `Sheaf.AlgebraicGeometry.Modules.BoundaryConnectingNaturality` states
`AlgebraicGeometry.Scheme.Modules.boundary_connecting_naturality`, with its sole proof
`sorry`. No definition or auxiliary theorem is introduced.

Hypothesis and clause correspondence:

- Arbitrary scheme X: `{X : Scheme.{u}}`. The explicit `HasExt.{u} X.Modules` is the
  universe bookkeeping required by the recorded Ext declaration; scheme modules are
  Grothendieck abelian, so this does not impose a geometric restriction.
- The short exact sequence 0 → A → E → C → 0: `S : ShortComplex X.Modules` and
  `hS : S.ShortExact`, with A = S.X₁, E = S.X₂, C = S.X₃.
- The module map C' → C: `{C' E' : X.Modules}` and `u : C' ⟶ S.X₃`.
- Its pullback short exact sequence with the SAME A: the maps
  `i' : S.X₁ ⟶ E'`, `p' : E' ⟶ C'`, `w' : i' ≫ p' = 0`, and
  `hT : (ShortComplex.mk i' p' w').ShortExact`. The comparison map is `v : E' ⟶ S.X₂`;
  `_hp : IsPullback v p' S.g u` states the actual universal pullback property,
  including the commuting right square. `_hi : i' ≫ v = S.f` fixes the canonical
  inclusion of A, excluding a twist of the kernel by an automorphism.
  These binders present the pullback sequence without choosing a particular limit;
  every pullback has this presentation. Short exactness is part of the sequence
  specified by the node, and is automatic for the canonical pullback of an epimorphism.
- Every t : O_X → C': `t : SheafOfModules.unit X.ringCatSheaf ⟶ C'`.
- The connecting boundary: `hS.extClass.postcomp O (zero_add 1)` is the actual
  connecting map Ext⁰(O,C) → Ext¹(O,A) in Mathlib's
  `Abelian.Ext.covariantSequence O hS 0 1 (zero_add 1)`. This was checked in
  Mathlib/Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean, in the definition
  `covariantSequence`, and its lemma
  `preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply`.
  Degree-zero morphisms enter it through `Abelian.Ext.mk₀`.
- The canonical Ext¹(O,A) = H¹(X,A) identification is used to WRITE the equality in
  Ext¹(O,A), as the node explicitly permits. This is equality before transport by the
  same canonical isomorphism on both sides, hence equivalent to equality after that
  transport. No new cohomology functor is defined, and the theorem does not replace
  module cohomology by the cohomology of an underlying abelian sheaf. In particular,
  it does not use `Scheme.Modules.H` as a second meaning of O_X-module cohomology.
- The asserted equality ∂_E(u ∘ t) = ∂_{u*E}(t): the left boundary is evaluated at
  `Abelian.Ext.mk₀ (t ≫ u)` and the right at `Abelian.Ext.mk₀ t`; the conclusion equates
  them in the same `Ext O S.X₁ 1`.

Dependency declarations read and used:

- `def-sc-ext-sheaf`: `AlgebraicGeometry.Scheme.Modules.Ext`, module
  `WeilConjectures.AlgebraicGeometry.Modules.Ext`. Its complete definition is the
  abbreviation `Abelian.Ext` on X.Modules, with `[HasExt.{u} X.Modules]`.
- `lem-sc-ext-locally-free`: module `Sheaf.AlgebraicGeometry.LocallyFreeExtCohomology`,
  `AlgebraicGeometry.Scheme.Modules.locallyFreeExtAddEquivH` and its unit specialization
  `locallyFreeUnitExtAddEquivH`. The module is imported. Its canonical identification
  explains the Ext-valued formulation, rather than inserting an arbitrary equivalence
  as a hypothesis. Its source also imports the recorded Ext definition. The displayed
  equality needs no choice of comparison since its codomain is already the same Ext
  group on both sides; the later bridge to `RingedSpace.moduleCohomology` is untouched.
- Mathlib `ShortComplex`, `ShortComplex.ShortExact`, `ShortComplex.ShortExact.extClass`,
  `Abelian.Ext.mk₀`, `Abelian.Ext.postcomp`, and `IsPullback` are reused directly.
  `IsPullback`'s full definition (commutative square and limiting cone) was read.

Edge cases checked before writing: empty scheme; zero A, E, C, or C'; t = 0; u = 0;
u = identity; split sequences. None requires nonemptiness, a field, finite rank, or
nonzero sections. The same A on both rows is essential: omitting `_hi` would allow
an unrelated identification of the kernel and could falsify the equality. All universes
and variables are explicit (`autoImplicit false`); no file-local notation or instance.

Searches (2026-10-11):

- msearch.py LeanSearch: “naturality of connecting maps in Ext under pullback short
  exact sequence”; unavailable, Internal Server Error (not a negative verdict).
- msearch.py LeanFinder: “naturality of sheaf module cohomology connecting boundary
  under pullback of short exact sequence”; eight unrelated group cohomology hits,
  no scheme-module specialization.
- msearch.py Loogle: `ShortComplex.ShortExact.extClass_naturality, Functor.rightDerived`;
  zero hits, unknown first identifier in the service's index. The local source DOES
  contain `extClass_naturality`, which was opened and read.
- msearch.py grep: `δ_naturality|extClass_naturality|connectingHom`, Algebra/Homology;
  nineteen hits: generic homology/triangle naturality and Ext-class naturality, no
  statement about sectionwise boundaries for the pullback module sequence.
- rg in WeilConjectures and lean/Sheaf: boundary/connecting/extClass and
  `covariantSequence|postcomp.*extClass`; found existing Ext and canonical comparison,
  plus sibling pushout/associativity statements, but no statement of this item.
- rg for the item's id in WeilConjectures: no hits. Declaration-name rg in Mathlib,
  WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json: no collision.

Sources opened online because this machine has no literature/stacks-project checkout:
https://stacks.math.columbia.edu/tag/05TE,
https://stacks.math.columbia.edu/tag/01DZ, and
https://stacks.math.columbia.edu/tag/0B3A.
The inherited source label describes 0B3A as pullback naturality, but 0B3A states the
canonical Ext/H¹ identification and boundary of 1. The naturality is supplied by 05TE;
this source-label fault is already documented in the base node's split_report.
No mathematical statement correction or disputed statement is needed.

Server single-file compile: passed, 2.4 seconds, no errors or warnings.


## Second reading by H1

I independently read the node, its two statement-dependency nodes and recorded
source modules, the delivery module, and the Mathlib definitions below. The
statement needs no repair; only this review section was added. There are no new
nodes, dependency modules, or statement corrections in this delivery.

Objects, hypotheses, and conclusion, matched in the node's order:

1. An arbitrary scheme X: `{X : Scheme.{u}}`. PASS. No field, characteristic,
   nonempty, Noetherian, separated, or finiteness condition is introduced.
   `[HasExt.{u} X.Modules]` is the same size bookkeeping as the recorded
   `Scheme.Modules.Ext` abbreviation, whose implementation note explains that
   scheme modules are Grothendieck abelian. It excludes no scheme in this universe.
2. A short exact sequence of O_X-modules, with objects A, E, C:
   `S : ShortComplex X.Modules`, `hS : S.ShortExact`, and respectively
   `S.X₁`, `S.X₂`, `S.X₃`. PASS. These are module sheaves, not abelian sheaves
   substituted for module sheaves, and ShortExact includes mono, exactness, epi.
3. An arbitrary O_X-module C' and morphism C' -> C:
   `{C' E' : X.Modules}` and `u : C' ⟶ S.X₃`. PASS. E' is the pullback's
   middle term introduced in the next clause, not an extra unrestricted sequence.
4. The pullback short exact sequence u*E with the same kernel A:
   `i' : S.X₁ ⟶ E'`, `p' : E' ⟶ C'`, `w' : i' ≫ p' = 0`,
   `hT : (ShortComplex.mk i' p' w').ShortExact`, and `v : E' ⟶ S.X₂`.
   `_hp : IsPullback v p' S.g u` supplies both the commuting right square
   and its universal property. `_hi : i' ≫ v = S.f` supplies the canonical
   kernel inclusion. PASS. Opening IsPullback shows that this is a limiting
   cone, not merely a commuting square. The left square is indispensable:
   twisting A by a nontrivial automorphism would change the boundary value.
   All pullbacks of the epimorphism S.g have the stated short exact sequence;
   hT records that specified row rather than imposing a new geometric condition.
   Presenting every pullback by its maps is equivalent to choosing one pullback.
5. The canonical Ext¹(O_X,A) = H¹(X,A) identification:
   both sides have codomain `Abelian.Ext (SheafOfModules.unit X.ringCatSheaf)
   S.X₁ 1`, definitionally the recorded `Scheme.Modules.Ext`. PASS.
   I opened `locallyFreeExtAddEquivH` and `locallyFreeUnitExtAddEquivH`, not
   just their names. The latter is the fixed canonical unit specialization,
   with no extra hypothesis on A. Equality before transport by this same
   injective comparison is equivalent to equality after transport. The formula
   does not introduce another H¹ definition or rely on an arbitrary equivalence.
   The existing comparison's target G.H and its bridge to the ringed-space
   module-cohomology convention are inherited; this item introduces neither.
6. Every t : O_X -> C':
   `t : SheafOfModules.unit X.ringCatSheaf ⟶ C'`. PASS. This unit is the
   structure module, so its Hom describes global module sections.
7. The sole equality, boundary_E(u composed with t) = boundary_u*E(t):
   `hS.extClass.postcomp O (zero_add 1) (Abelian.Ext.mk₀ (t ≫ u)) =
   hT.extClass.postcomp O (zero_add 1) (Abelian.Ext.mk₀ t)`, with O the
   displayed structure module. PASS. I read `Ext.postcomp` (Basic.lean:407),
   `covariantSequence` (ExactSequences.lean:128), and
   `preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply` (line 50).
   These identify the displayed map with the actual connecting map, with
   composition in the right direction and no missing sign. Quantification
   is first over the sequence, then u and its pullback, then every t.

Source check: there is no local Stacks checkout. I fetched the raw Stacks
cohomology.tex and derived.tex into this item's scratchpad and read
`lemma-h1-extensions` (cohomology.tex:348), the opening module-cohomology
paragraph (lines 61-75), and `lemma-right-derived-delta-functor`
(derived.tex:5683). I also checked the corresponding official pages:
https://stacks.math.columbia.edu/tag/0B3A,
https://stacks.math.columbia.edu/tag/01DZ, and
https://stacks.math.columbia.edu/tag/05TE.
They assume a ringed space and its module sheaves, with enough injectives;
no additional scheme hypothesis is needed. Tag 0B3A supplies the canonical
Ext/H¹ identification and the boundary of 1, not a separate naturality lemma.
Tag 05TE supplies the delta-functor structure. The inherited source-label
fault is already recorded in split_report and correctly distinguished by
the delivery docstring; it does not warrant changing the node's statement.

Edge cases: the empty scheme and zero modules are included. The zero map u,
zero section t, identity u, and split sequences are included. No empty index
set occurs; no characteristic is fixed; degree zero is used as Ext⁰ input
and degree one as output, exactly as the node requires. Universe u is bound
and arbitrary; all sheaves have the same size as the dependency encoding.
The map named u shadows the universe name only in the term context; neither
is unbound. No independent index universe or smallness restriction appears.

Independent searches, with vocabulary different from the first reader:

- LeanFinder: `Ext zero degree boundary functorial Cartesian square sheaves`.
  Eight hits, mostly Mayer-Vietoris square constructions and Sheaf.H; none
  states this sectionwise pullback boundary equality.
- Loogle: `CategoryTheory.ShortComplex.ShortExact.extClass_naturality`.
  One hit. I read ExtClass.lean:131: it equates compositions of extension
  classes for a general morphism of short exact sequences. It does not
  itself quantify over t or state the connecting-map evaluation here;
  using it requires forming (id,v,u), composing with mk₀ t, and associativity.
  Thus this delivery is not a second copy of that declaration.
- LeanSearch: `Ext connecting homomorphism is natural for Cartesian short
  exact module sequences`. Service returned Internal Server Error;
  recorded as unavailable, not as a negative search result.
- msearch grep `extClass_naturality|postcomp` in DerivedCategory/Ext:
  17 hits. Opened the boundary and composition definitions listed above.
- Independent rg of WeilConjectures, repository lean/Sheaf and Mathlib Ext
  with `extClass_naturality|mk₀.*comp|comp.*mk₀|boundary_connecting|connecting.*natural|boundary.*natural`,
  plus `boundary|connecting|extClass|covariantSequence` in the module-sheaf
  directories: generic Ext naturality and sibling pushout/associativity
  declarations, no existing statement of this item. No new notion is needed.

H5/H6/H8/H9 check: no new definition, hollow data, local notation, local
instance, private copy, auxiliary theorem, or proved result. The one theorem
has precisely `by sorry`. The header and declaration docstring identify the
sources and blueprint item; the docstring reproduces both proof steps and
names their dependency nodes. Lines are at most 100 characters. Imports
provide the recorded Ext/comparison dependency and IsPullback. Every binder
is explicit under autoImplicit false. The node's lean.statement was checked
programmatically to be verbatim the theorem signature before `:= by`.

Validation: the prescribed scompile.py command passed on the server in
2.0 seconds, with exit code 0 and no errors or warnings. No mathematical or
Lean change was necessary; the worker's correct statement was preserved.
