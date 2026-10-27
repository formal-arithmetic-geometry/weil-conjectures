## Worker report

This delivery states `AlgebraicGeometry.semiabelian_trait_hom_extension` in
`Sheaf.AlgebraicGeometry.SemiabelianTraitHomExtension`. Its only proof is `sorry`.
The accepted statement, split, dependencies and source are unchanged; only `lean`
is added. No new definition or dependency module is needed.

The previous worker's stage-1 live-wins refusal does not apply: the current
coord/brief-stage2.md section 0 explicitly allows formalizing a passing split.
The queue lists this item at stage 2, and the node has no Lean record. There is
no repair note for it. The example CompactObject module is now withdrawn; I read
its current node, which binds the upstream declaration, and followed current
module-mode conventions used by SemiabelianGeometricFibres instead.

Hypothesis and clause mapping:

- The DVR is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. Mathlib's class is a local PID which is not a
  field; it matches def-sc-discrete-valuation-ring, including the nonfield clause.
- The fraction field is `(L : Type u) [Field L] [Algebra R L]
  [IsFractionRing R L]`. This permits every choice of fraction-field model,
  rather than a field extension or an arbitrary field. The trait is literally
  `Spec (.of R)` throughout. Both ring and fraction field use the scheme universe;
  every fraction field has a model in that universe, as in the library convention.
- `G H : Grp (Over (Spec (.of R)))` supplies the actual multiplication, identity
  and inverse morphisms over the trait and all group identities.
  `[IsCommMonObj G.X] [IsCommMonObj H.X]` supplies commutativity. Morphisms in
  this category preserve the given group structures, not separately chosen laws.
- `[Smooth G.X.hom]` and its H counterpart render smoothness.
- `[IsSeparated G.X.hom]` and its H counterpart mean exactly closed-immersion
  diagonals, by the recorded Mathlib definitions; no properness is imposed.
- Finite presentation is `[LocallyOfFinitePresentation G.X.hom]
  [QuasiCompact G.X.hom]`, and the same for H. Quasi-separatedness follows from
  the already stated separatedness. Thus this is finite presentation, not just
  local finite presentation. This is also the established encoding in the
  NormalSemiabelianHomExtension module.
- `hG : HasSemiabelianGeometricFibres G` and `hH` use the dependency declaration
  verbatim: for each algebraically closed field and geometric point, a split
  torus kernel, abelian quotient and fppf locally surjective quotient map.
- `Spec.map (CommRingCat.ofHom (algebraMap R L))` is the canonical inclusion
  of the generic point. `(Over.pullback ...).mapGrp.obj G` and its H counterpart
  are exactly the generic fibres with their induced group structures. The
  chosen fibre product is the same construction as Scheme.Hom.fiber, with the
  generic residue field identified with the fraction field as the node's proof
  instructs. No arbitrary comparison map replaces base change.
- `v` is a morphism between those group objects, hence an L-group homomorphism.
- `∃! vbar : G ⟶ H, (Over.pullback ...).mapGrp.map vbar = v` expresses both
  existence and uniqueness of the T-group homomorphism and exact restriction
  to the specified v. It does not assert uniqueness merely up to isomorphism.
- There are no completeness, excellence, residue-characteristic, perfection or
  properness binders. Mixed and equal characteristic and noncomplete DVRs remain.

Dependencies read and used:

- Mathlib.RingTheory.DiscreteValuationRing.Basic: `IsDiscreteValuationRing`.
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`, underlying the scheme and affine-spectrum nodes.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `AlgebraicGeometry.Smooth`.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  `AlgebraicGeometry.IsClosedImmersion`; the imported Separated module defines
  `AlgebraicGeometry.IsSeparated` by this diagonal condition.
- Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres:
  `AlgebraicGeometry.HasSemiabelianGeometricFibres` (full definition read).
- Mathlib.AlgebraicGeometry.Fiber: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, the generic-fibre convention.
- WeilConjectures.AlgebraicGeometry.BaseChangeConventions: plain proof import
  for def-pc-base-change. Read its complete definitions and comparison statements;
  scheme/group base change uses the shared `Over.pullback` and `Functor.mapGrp`.
- Mathlib.RingTheory.Localization.FractionRing: `IsFractionRing`.

The proof dependency lem-sfb-trait-semiabelian-hom-extension is an existing DAG
node but has no Lean record or module, so there is no proof import to add for
it yet (stages/2-statements.md section 3.7 imports stated proof dependencies).
It is not needed to type this statement. Its text was read and agrees with
this item after renaming F to L. I retained the accepted proof plan verbatim
in substance in the theorem docstring. I did not import the more general
normal-base extension theorem: it is downstream of this trait input and would
risk an import cycle. The old twin-node duplication remains a maintainer issue;
this delivery does not create a second Lean declaration for the twin.

Source checked: the primary Faltings scan at
https://www-fourier.univ-grenoble-alpes.fr/~lefourns/contenu/Zywina/Faltings.pdf,
Chapter II section 2 Lemma 1, printed pages 10-11. It states unique extension
on a normal base and identifies the complete DVR case at the start of its proof.
The arbitrary-DVR input and the accepted split's reuse of the twin are preserved.
No source-based statement correction is required.

Edge cases checked mathematically: zero groups (rank zero is explicitly allowed
in the shared fibre definition); split tori and their power maps including the
zero homomorphism; abelian schemes; semiabelian schemes whose toric ranks jump;
positive and mixed characteristic; noncomplete and nonexcellent DVRs. Empty
scheme group objects over this nonempty trait are already excluded by the
identity section, as in the mathematical statement. A field is excluded as a
DVR by the existing class, not by an added hypothesis. No counterexample or
STATEMENT-DISPUTED flag was found.

Searches (actual msearch.py results are retained in searches.jsonl):

- LeanFinder: "A group homomorphism between the generic fibres of smooth
  separated semiabelian group schemes over a discrete valuation ring extends
  uniquely over the ring": eight hits, valuative criteria and valuation-ring
  maps; none is a semiabelian homomorphism extension theorem.
- Loogle: `"semiabelian"`: zero hits.
- Mathlib grep: `semi.?abelian|homomorphism.*trait|trait.*homomorphism`
  in AlgebraicGeometry: zero hits.
- LeanSearch: "Homomorphisms of smooth semiabelian schemes over a discrete
  valuation ring are determined by and extend from their generic fibres":
  eight hits on smoothness, scheme/module morphisms and smooth ring maps,
  none giving this theorem.
- rg in WeilConjectures and Sheaf for semiabelian, trait and extension found
  the existing shared fibre definition and the broader normal-base theorem.
  The latter has a normal integral locally Noetherian base, so is not the same
  statement and lies above this input in the proof DAG. Searching the item id
  in WeilConjectures found no declaration. No exact reusable declaration exists.

Validation: scompile.py compiled the delivered module separately in sandbox
and library modes against the live published build, both clean (2.5 seconds
per mode). Auto-implicit variables are disabled; the universe is explicit.
The report's subsequent dry run validates preflight and compilation again.

## Second reading by Q71

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
