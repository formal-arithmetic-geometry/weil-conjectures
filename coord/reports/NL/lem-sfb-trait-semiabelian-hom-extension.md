## Worker report

This delivery records the exact existing declaration
`AlgebraicGeometry.semiabelian_trait_hom_extension` in
`Sheaf.AlgebraicGeometry.SemiabelianTraitHomExtension`, already landed and reviewed
for `lem-sfb-semiabelian-trait-hom-extension`. No Lean module is added and no
statement, dependency list, or proof is changed. Only this item's `lean` field is
set, with `existing: true`. I read the complete declaration and its docstring,
the twin's statement and reviewed Lean record, and every statement dependency's
statement, record and source declaration. The item's fraction field F is named L
in the existing declaration; this is only a bound-variable renaming.

Clause-by-clause correspondence:

- The DVR R is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. Mathlib's class is exactly a local principal ideal
  domain with nonzero maximal ideal, excluding fields.
- F = Frac(R) is `(L : Type u) [Field L] [Algebra R L]
  [IsFractionRing R L]`. This permits any realization of the fraction field;
  it does not choose an arbitrary extension field.
- T = Spec R is `Spec (.of R)` in `G H : Grp (Over (Spec (.of R)))`.
  The actual group objects include multiplication, unit, inverse and their laws
  as morphisms over T. `IsCommMonObj G.X` and `IsCommMonObj H.X` impose the
  commutative group identities.
- Smoothness is `[Smooth G.X.hom] [Smooth H.X.hom]`.
- Separatedness is `[IsSeparated G.X.hom] [IsSeparated H.X.hom]`.
  I read the Mathlib class: it means exactly that `pullback.diagonal` is a
  closed immersion; this is the clause explained in the node.
- Finite presentation is `LocallyOfFinitePresentation` together with
  `QuasiCompact` for each structure map. The remaining quasi-separated condition
  follows from the already assumed separatedness. No finite-type hypothesis is
  added or substituted, and neither group is required to be proper.
- Semiabelian geometric fibres are the hypotheses
  `hG : HasSemiabelianGeometricFibres G` and
  `hH : HasSemiabelianGeometricFibres H`, using the recorded declaration verbatim.
  Its definition quantifies over algebraically closed field-valued points and
  uses the induced group-object pullback, a split torus kernel square, an abelian
  variety quotient, and fppf local surjectivity. Rank zero is allowed.
- The generic group fibres are
  `(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mapGrp.obj G`
  and the analogous object for H. The contravariant `Spec.map` has precisely
  source Spec L and target Spec R. `Over.pullback` forms the specified fibre
  product, and `mapGrp` transports the actual group operations.
- The given F-group homomorphism v is a categorical morphism between these
  two group objects; it is not an arbitrary morphism of their underlying schemes.
- The extension is `vbar : G ⟶ H`, again an actual T-group homomorphism.
  `∃! vbar : G ⟶ H, ...mapGrp.map vbar = v` gives existence and uniqueness
  together, with exact agreement on the generic fibre under canonical pullback.
- There is no completeness, excellence, residue-field perfection, residue
  characteristic, or properness assumption. There is no independent dimension,
  torus-rank constancy, or abelian-generic-fibre restriction.

Dependency declarations read and used by the existing statement:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.Spec`,
  `AlgebraicGeometry.Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres`:
  `AlgebraicGeometry.HasSemiabelianGeometricFibres`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; used through
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`:
  `AlgebraicGeometry.IsSeparated`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: read the whole
  recorded bundle, including `Scheme.Modules.moduleBaseChange`,
  `baseChange_morphism_projections`, `baseChange_iterated`, `baseChange_fiber`,
  `Scheme.Hom.geometricFiberAt`, and `baseChange_section_characterization`.
  Its scheme base-change interface is Mathlib's `CategoryTheory.Over.pullback`,
  not its module-only `moduleBaseChange`. The existing theorem uses exactly this
  `Over.pullback` interface and its `CategoryTheory.Functor.mapGrp` lift.
- `Mathlib.RingTheory.Localization.FractionRing`: `IsFractionRing`.

Edge cases checked before recording: pure tori (rank zero abelian quotient),
abelian schemes (rank zero torus), the trivial group, zero and identity
homomorphisms, positive and mixed residue characteristic, imperfect residue
fields and noncomplete DVRs. No empty group fibre is silently allowed: a group
object has its identity section. A field is intentionally excluded as a DVR.
The single arbitrary universe u contains the ring, fraction field and schemes;
no extra equality of independently meaningful site universes is imposed. No
properness or constant toric-rank restriction excludes degenerating families.

Searches, all on 2026-10-24 using the prescribed msearch wrapper:

- LeanFinder: “A homomorphism between generic fibres of smooth semiabelian group
  schemes over a discrete valuation ring extends uniquely over the ring” returned
  8 general valuative-criterion declarations, not this group-homomorphism theorem.
- Loogle: `"Semiabelian", "Hom"` returned no hits.
- Mathlib grep: `semi.?abelian|generic.*hom.*exten` in AlgebraicGeometry returned
  no hits.
- LeanSearch: “Homomorphisms of semiabelian schemes over a discrete valuation ring
  extend uniquely from the generic fibre” returned 8 general extensionality and
  valuative-uniqueness declarations, none stating this result.
- Repository rg: `semiabelian.*(extension|hom)|semiabelianHom|trait.*semiabelian|` 
  `lem-sfb-trait-semiabelian-hom-extension` in both `lean/WeilConjectures` and
  `lean/Sheaf` found the exact declaration in
  `lean/Sheaf/AlgebraicGeometry/SemiabelianTraitHomExtension.lean` and the more
  general normal-base extension statement. The exact match is reused.

The primary-source scan was opened at
https://www-fourier.univ-grenoble-alpes.fr/~lefourns/contenu/Zywina/Faltings.pdf .
Chapter II, section 2, Lemma 1, printed pp.10–11 states extension over a normal
base from a dense open, with the complete-DVR case as its opening proof input.
This delivery makes no source-based correction and does not assert that the
arbitrary-DVR input is printed there as a separate lemma.

Process handoff for independent review: the two DAG nodes are mathematical
statement duplicates, already identified in their stage-1 reviews. The existing
declaration's docstring currently follows the twin node's proof plan by applying
this item. Attaching this item to that same declaration is statement reuse, not
a proof or an attempt to discharge the theorem by itself. At stage 3 the shared
declaration must be proved using THIS item's accepted independent Néron-model
proof (its four existing proof steps), rather than the twin's self-application
plan. No theorem is proved here. The current item's independent proof and
proof_deps are preserved verbatim. Proof-only declarations already available
include `semiabelian_geometric_power_integrality` and
`locallyAlgebraicGroup_identityComponent`; the Néron existence and open-immersion
criterion nodes have no recorded Lean declarations yet. No new proof import is
introduced because this delivery adds no module and must not edit another
node's existing module. Canonicalization of the duplicate and stage-3 import
maintenance remain maintainer work. No mathematical statement dispute found.

Validation: deliver2.py's dry run checks the existing declaration by a private
server-side #check through scompile.py and runs the maintainer preflight. There
are no delivered Lean files requiring a separate file compile.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
