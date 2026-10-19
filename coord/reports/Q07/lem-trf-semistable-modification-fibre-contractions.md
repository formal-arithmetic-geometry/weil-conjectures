## Worker report

The module `Sheaf.TraceFormula.SemistableModificationFibreContractions` states
`AlgebraicGeometry.semistable_modification_fibre_contractions`, with its proof `sorry`.
The real recursive definition
`AlgebraicGeometry.MultipointedPair.HasExceptionalContractionSequence` spells out the
finite factorization in this very node. It is an owning-node helper, not an existence
axiom or an independent substitute for semistability. It chooses no schemes or maps.

Source read: Temkin, Stable modification of relative curves,
https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf,
Section 1.2 (printed p. 2), Lemma 4.4.2 and Corollary 4.4.3(i) (printed pp. 30–31),
and the elementary contraction paragraph before Lemma B.3 (printed p. 58).
The last paragraph specifies both the scheme pushout and the unchanged marking.
The module docstring carries the node's nine-step proof, including the independent
terminal finite nodal map criterion; it does not invoke stable-blowdown uniqueness.

Hypothesis and clause correspondence:

- `K : Type u`, `[Field K]`, `[IsSepClosed K]` are the given separably closed field.
- `V : ValuationSubring K` is literally a valuation subring of K. Its `mem_or_inv_mem`
  is the valuation condition. Its existing `IsFractionRing V K` instance supplies exactly
  the fraction-field condition; there is no extra discretely-valued or Noetherian assumption.
- `[Finite (PrimeSpectrum V)]` is the finite-chain hypothesis: valuation-ring primes are
  already totally ordered. This includes the case V is a field.
- `Spec (.of V)` and `Spec.map (CommRingCat.ofHom V.subtype)` are S and eta -> S.
- `P Q : MultipointedCurve (Spec (.of V))` are the two multipointed relative curves.
  The recorded structure retains flatness, finite presentation (including qc and qs),
  pure relative dimensions 1 and 0, and the closed marking immersion.
- `q : P.Hom Q` is the compatible pair of S-morphisms, with `curve_over`,
  `marking_over` and `comm` from the recorded dependency.
- `hq : q.IsEtaModification ...` is precisely properness on both parts, isomorphisms
  on schematically dense opens of both parts, and the prescribed generic isomorphisms.
- `hP` and `hQ` use the recorded `MultipointedCurve.IsSemistable` without a private copy.
- `hQη : Smooth (pullback.snd Q.x ...)` and
  `hNη : Etale (pullback.snd Q.d ...)` are the generic smoothness and etaleness hypotheses.
- `s : Spec (.of V)` is arbitrary. `Ω : Type u`, `[Field Ω]`,
  `[Algebra ((Spec (.of V)).residueField s) Ω]` and `[IsAlgClosure ... Ω]` allow
  every algebraic closure with its specified residue-field embedding, not only the
  distinguished `AlgebraicClosure`. There is no independent smaller test universe.
- The repeated map `Spec.map (CommRingCat.ofHom (algebraMap ... Ω)) ≫
  (Spec (.of V)).fromSpecResidueField s` is exactly the geometric point over s.
  `MultipointedPair.ofCurve` forgets only proofs, and `.baseChange` uses the canonical
  pullback of schemes and markings. `Over.pullback ... |>.map` gives exactly q_Omega
  on the curve and marking. The initial maps are specified, never existentially chosen.
- `∃ n : ℕ, HasExceptionalContractionSequence Ω n ...` asserts a finite factorization.
  At n=0 the supplied remaining curve and marking maps are isomorphisms, and the
  marking square commutes: exactly a final isomorphism of pairs and an empty composite.
- At n+1, `R`, `h`, `hd`, `r`, `rd` give the next pair, the elementary contraction
  on the curve and marking, and its remaining map to the fixed target. The equations
  `h ≫ r = f` and `hd ≫ rd = d` make the composite the original map on BOTH parts.
  Recursive compatibility of `r,rd` and `P.inclusion ≫ h = hd ≫ R.inclusion`
  give compatibility of every intermediate map with the markings.
- `P.IsSemistable` and `R.IsSemistable` retain semistable pointed curves at each step.
  These predicates are the landed pair predicates, defined through the same
  multipointed-curve structure and the scalar-compatible ordinary-double-point predicate.
- `a : ProjectiveLine (Spec (.of Ω)) ⟶ P.curve.left`, `IsClosedImmersion a`,
  the equation over Spec Omega, and `Set.range a ∈ irreducibleComponents ...` say
  that A is an irreducible component isomorphic OVER Omega to the projective line.
- `(Set.range a ∩ (Set.range P.inclusion.left ∪
  {x | ¬ (P.curve.hom.stalkMap x).hom.FormallySmooth})).encard ≤ 2` counts distinct marked or singular
  points on the component itself, without normalization-branch multiplicities.
- `(Set.range (a ≫ f.left)).Subsingleton` is singleton image under the remaining
  target map: the range is nonempty since the projective line over a field is nonempty.
- `b : Spec (.of Ω) ⟶ R.curve.left` over Spec Omega and
  `IsPushout a (ProjectiveLine ... ↘ Spec (.of Ω)) h.left b` assert the actual scheme
  pushout, with universal property against all schemes in the ambient universe.
  No general existence of scheme pushouts is assumed.
- `IsProper h.left` is properness of each elementary quotient map.
- The open U is exactly the complement of `Set.range b`; its inverse image is exactly
  the complement of `Set.range a`; `IsIso (pullback.snd h.left U.ι)` says that the
  quotient map is an isomorphism away from A.
- `IsIso hd` and the marking square identify the new closed marking scheme with the
  image of the old marking, including its scheme structure, and supply its isomorphism.
- No connectedness, separatedness or properness instance is imposed on P.x or Q.x.
  Finite presentation includes quasi-separatedness, which is weaker than separatedness.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (the separably-closed half of
  def-kun-separably-closed, whose record also includes `IsSepClosure`).
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Sheaf.TraceFormula.MultipointedCurve`: `AlgebraicGeometry.MultipointedCurve`.
- `Sheaf.AlgebraicGeometry.MultipointedCurveModification`:
  `MultipointedCurve.Hom`, `.IsEtaModification`, `MultipointedCurve.IsSemistable`;
  read the full base-change, marking, special-point and stability interfaces too.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.fromSpecResidueField`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure`; the concrete
  `AlgebraicClosure` declaration is not substituted for the arbitrary closure.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`: read the recorded
  `ProjectiveLine.TwistData`; its imported `ProjectiveLine` is the scheme used here.
  No replacement for the projective line or its standard-cover definition is introduced.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- Added the already landed `def-trf-semistable-multipointed-pair` to stmt_deps:
  `Sheaf.AlgebraicGeometry.SemistableMultipointedPair`, `MultipointedPair`,
  `MultipointedPair.ofCurve`, `.baseChange`, `.IsSemistable`. This gives canonical
  geometric-fibre pairs without choosing missing property proofs by a sorry theorem.
- `Mathlib.RingTheory.Valuation.ValuationSubring`: `ValuationSubring` and its
  `IsFractionRing` instance. `CategoryTheory.IsPushout` is the existing categorical
  pushout predicate, specialized to schemes.

All proof dependencies having recorded modules are imported without `public`:
FiniteBirationalNormalIso, GeometricallyReducedEtaNormal, SemistableMarkedBaseChange,
ValuationHorizontalCurveModels, Mathlib ZariskisMainTheorem, Noetherian. Proper
permanence is already publicly imported through MultipointedCurveModification.
Unstated proof-only prerequisites (finite-birational-nodal-connected-iso,
nodal-exceptional-component-pushout, nodal-subcurve-boundary,
proper-normal-geometric-connectedness, valuation-curve-projective-preparation,
valuation-exceptional-local-criterion) remain explicit in the proof plan; they introduce
no object needed to type this statement, so no substitute theorem is introduced.

Edge cases checked before writing: identity modification and no exceptional component
(n=0); empty marking (all its isomorphism/compatibility assertions remain meaningful);
empty curve fibre (no component is demanded in the zero branch); disconnected curves
(no connectedness binder); nonproper or nonseparated structural maps; valuation subring
that is the whole field; positive characteristic including imperfect separably closed K;
an arbitrary algebraic closure and its given embedding; exactly zero, one or two distinct
special points, counted by encard; nodal points remain singular in the ambient curve even
when smooth on the embedded component. The positive-length branch cannot contract an
empty component because its source is the projective line over a field.

Searches performed:

- LeanFinder: “A semistable pointed curve modification over a valuation ring induces a
  finite sequence of contractions of exceptional projective line components on every
  geometric fibre”: eight elliptic-curve minimal-model results; no match.
- Loogle: `AlgebraicGeometry.IsProper, AlgebraicGeometry.Scheme.Hom`: zero hits.
- Mathlib grep through msearch: `semistable|semi_stable|blowdown|exceptional.*tree`:
  zero hits.
- LeanSearch: “Finite composite of elementary exceptional projective line component
  pushout contractions of nodal marked curves”: eight hits about finite morphisms and
  categorical pushout pasting; none is this geometric statement.
- `rg` of the upstream WeilConjectures and side lean/Sheaf trees for exceptional
  contractions, contracted components and semistable fibres found adjacent curve-tree
  and domination lemmas, but no finite elementary pushout factorization declaration.
  The exact blueprint id is absent upstream. Searches of `dag/lean_names_upstream.json`
  and both Lean trees for the proposed declaration names found none.
- DAG search and `tools/blueprint_refs.py search contraction` found no separate
  elementary-contraction-sequence definition node; neighboring nodes use contractions
  in proofs. The existing underlying-pair node provides the needed base-change interface.

No node statement correction, no dependency record repair, and no disputed statement.
The only statement-dependency addition is the existing underlying-pair definition.

Compiler repair: on an underlying pair the finite-presentation proof is contained in
IsSemistable, rather than a typeclass binder. Therefore the special-point set uses
the identical stalk-formal-smoothness predicate of the landed pair interface instead
of calling smoothLocus with an unavailable implicit instance. No hypothesis or
new smoothness definition was introduced.

Validation: scompile.py compiled the sandbox and final library module cleanly, with no
errors or warnings. The delivery dry run printed “OK (dry run): commit 15d3389497
passes the preflight and compiles; nothing pushed”. All variables and the universe u
are explicitly bound, autoImplicit is disabled, and the maximum Lean line width is 97.
The only postponed proof is the named main theorem; the recursive definition has real data.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
