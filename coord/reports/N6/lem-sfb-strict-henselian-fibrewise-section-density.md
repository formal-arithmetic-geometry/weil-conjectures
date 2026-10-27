## Worker report

This stage-2 delivery states `AlgebraicGeometry.Scheme.strictHenselian_fibrewiseSection_dense`
in `Sheaf.AlgebraicGeometry.StrictHenselianFibrewiseSectionDensity`, with `sorry` as its
only proof. It changes only the item's `lean` record. The accepted NO stage-1 split,
statement, proof, dependencies, source and review remain intact. The prior BLOCKED ending
confused completion of stage 1 with completion of stage 2: the live node is split but has
no Lean record, and coord/queue.tsv lists it at stage 2. The stage-handoff paragraph of
coord/brief-stage2.md explicitly permits this statement delivery.

Clause correspondence:

- The Noetherian commutative ring R is `(R : Type u) [CommRing R] [IsNoetherianRing R]`.
- Strict henselian locality is `[IsStrictlyHenselianLocalRing R]`. Its existing class
  extends `HenselianLocalRing`, hence `IsLocalRing`, and has separably closed residue field.
- The scheme and specified structure map are `{X : Scheme.{u}}` and
  `(f : X ⟶ Spec (.of R))`.
- Smoothness is `[Smooth f]`.
- Separatedness is `[IsSeparated f]`, defined in Mathlib as closed immersion of the
  diagonal, exactly the inline definition in the node.
- Finite presentation is the conjunction of local finite presentation, quasi-compactness,
  and quasi-separatedness. Smoothness supplies local finite presentation; the binder
  `[QuasiCompact f]` supplies quasi-compactness; separatedness supplies quasi-separatedness.
  Thus no global finite-presentation hypothesis has been lost by keeping only the
  additional `[QuasiCompact f]` binder. The node def-sbc-locally-finite-presentation states
  precisely this global/local comparison.
- The given section is `(e : Spec (.of R) ⟶ X) (he : e ≫ f = 𝟙 _)`.
- Geometric irreducibility of every residue-field fibre is
  `[GeometricallyIrreducible f]`. Mathlib's
  `GeometricallyIrreducible.iff_geometricallyIrreducible_fiber` identifies this with
  `∀ q, GeometricallyIrreducible (f.fiberToSpecResidueField q)`.
- Every prime q and every algebraically closed extension Ω/κ(q) are encoded by
  `(Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of R))`.
  `Scheme.SpecToEquivOfField Ω (Spec (.of R))` is the existing equivalence from t to
  a point q together with the field embedding κ(q) → Ω, whose inverse is
  `Spec.map ρ ≫ (Spec (.of R)).fromSpecResidueField q`. Thus this is equivalent
  parameterization, not a restriction to the closed point or to algebraic closures.
  No `IsAlgClosure`, algebraicity, characteristic or finite-degree assumption occurs.
- The geometric fibre is the recorded fibre product `pullback f t`; the arbitrary
  nonempty open is `(W : Set ↥(pullback f t)) (hW : IsOpen W) (hWne : W.Nonempty)`.
- The conclusion gives a global R-section `a` with `a ≫ f = 𝟙 _`. Its induced Ω-point
  is `b : Spec (.of Ω) ⟶ pullback f t`, constrained by BOTH equations
  `b ≫ pullback.fst f t = t ≫ a` and `b ≫ pullback.snd f t = 𝟙 _`.
  These characterize the unique pullback lift, so b is not an arbitrary point or
  supplied comparison. Its value `b default ∈ W` is membership at the unique point
  of Spec Ω. Existence of this b adds no mathematical hypothesis or stronger conclusion:
  the pullback universal property always constructs it from a's section equation.
- Meeting every nonempty open is exactly the stated Zariski-density reformulation.
  No group, commutativity, properness, affineness or group operation is assumed on X.

Dependency declarations read and used:

- def-weil-pbc-noetherian-ring: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs` (Noetherian as a module over itself, equivalently
  every ideal finitely generated).
- def-weil-pbc-henselian-terminology: `IsStrictlyHenselianLocalRing`,
  `WeilConjectures.Mathlib.RingTheory.Henselian` (class and its equivalence with
  henselian locality plus separably closed residue field read).
- def-pc-scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; also `AlgebraicGeometry.Spec` and `Spec.map`.
- def-sbc-smooth-morphisms: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth` (affine-local smooth ring maps).
- def-sbc-locally-finite-presentation: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`; its role in global finite
  presentation is provided by the smoothness instance and the two global conditions above.
- def-pc-geometrically-irreducible: `AlgebraicGeometry.GeometricallyIrreducible`,
  imported through its recorded `Mathlib.AlgebraicGeometry.Geometrically.Integral` module.
  The full definition and fibre equivalence in Geometrically.Irreducible were read.
- def-weil-residue-field: `Scheme.residueField` and `Scheme.Hom.residueFieldMap`,
  `Mathlib.AlgebraicGeometry.ResidueField`. The existing `SpecToEquivOfField` in this
  same module justifies the geometric-point parameterization. No residue field was copied.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, with scheme pullbacks
  supplied by the geometry imports.
- def-weil-algebraic-closure: Mathlib match includes `IsAlgClosed` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`; this is the clause used, not `IsAlgClosure`.

Stated proof-dependency modules are imported without `public`: EtaleLocalNormalForm,
Etale.QuasiFiniteAtPrime, AffineSpace, Morphisms.UniversallyOpen, RingTheory.Etale.Basic,
RingTheory.QuasiFiniteAtPrime, QuasiFiniteMorphism, and Sites.StrictlyHenselian.
The proof-only import of the latter is the recorded module of
lem-sbc-strict-henselian-etale-neighbourhood-section. The newly split
lem-sfb-quasifinite-closed-nowhere-dense-image has no Lean record yet, hence no module
can be imported; it remains named explicitly in the six-step proof docstring.

Source: I read `more-morphisms.tex`, `lemma-etale-nbhd-dominates-smooth` (055U), including
both proofs, and the current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`.
055U gives étale-local sections, not this stronger density statement. The source annotation
and the accepted agent-written six-step density proof are retained honestly in the docstring.
The complete accepted node proof was read before writing the statement.

Edge cases checked: R a separably closed field (only closed prime); a strictly henselian
DVR with X = affine line or multiplicative group (closed and generic primes); a nonreduced
Artinian strict local ring (no reducedness on R added); relative dimension zero (chart
polynomials are constants); any characteristic; Ω of positive transcendence degree; W empty
(the explicit nonempty premise excludes it); X empty (the supplied section over nonempty
Spec R excludes it, as in the node). The use of b requires its second projection to be the
identity, so a geometric point with a nontrivial field self-map is not accidentally used.
All parameters and universe u are explicitly bound, with autoImplicit false. The common
scheme/field universe is Mathlib's convention; u is arbitrary and can be increased for any
chosen extension field, so it is not an independent smaller test universe.

Searches actually run with msearch.py for N6 and this item:

- LeanFinder: "Sections of a smooth scheme over a strictly henselian local ring are
  Zariski dense in every geometric fibre". Eight hits about dominant morphisms and dense
  partial-map domains; none about values of global strict-local sections.
- LeanSearch: "Sections of a smooth scheme over a strictly henselian local ring meet
  every nonempty open subset in every geometric fibre". Eight hits about integral-scheme
  sections, smoothness and germ maps; none states the item.
- Loogle: "IsStrictlyHenselianLocalRing, Dense" returned zero hits with unknown identifier
  IsStrictlyHenselianLocalRing (upstream, not a Mathlib name); this is not counted as a
  successful exhaustive negative. A further query `"HenselianLocalRing", "Dense"`
  returned zero hits without the unknown-identifier note.
- Mathlib grep (AlgebraicGeometry): `henselian.*dense|dense.*henselian|section.*dense|dense.*section`
  returned only the Birational.lean `section DenseOpen` hit.
- rg in lean/WeilConjectures and lean/Sheaf for the blueprint id and the henselian/dense
  and section/dense patterns: no exact item declaration. I opened DensePoints.lean:
  `Scheme.Hom.denseRange_fieldPoints` and `denseRange_baseChangeFieldPoint` concern a
  separably closed FIELD base, not a strictly henselian local ring and all its primes.
  IntegralStrictHenselianGeometricFibreSections is a cohomological-section restriction
  theorem for integral morphisms, not density of scheme sections for smooth morphisms.

No new notion, dependency module, statement correction, or statement dispute is needed.

## Second reading by N6

This is a second pass by the same dispatcher-started worker; the prompt expressly forbids
starting another agent. The maintainer's independent review remains required. I reopened
the accepted JSON statement and the final Lean file and checked each clause listed above.

The checks caught and repaired two draft issues before delivery: local finite presentation
alone did not state the node's global finite presentation, so I used QuasiCompact f together
with smoothness and separatedness; the pullback used as a set's element type needed the
explicit scheme-to-type coercion `↥`. The final statement retains Noetherianity, strict
henselianity, all three geometric finiteness/separation conditions, the given section,
geometric irreducibility of every fibre, all algebraically closed extensions, every
nonempty open, and a global section whose uniquely specified base change lies there.

I checked specifically that t is arbitrary rather than merely the closed geometric point,
that IsAlgClosed does not impose algebraicity, that GeometricallyIrreducible f is equivalent
to the fibre-by-fibre premise, and that BOTH projection equations pin down b. The second
projection is the identity, rather than only equality on underlying topological points.
No conclusion about a group operation or any prescribed value of a at the closed point
is asserted. The additional b witness is forced by the universal property, as the item's
phrase "induced Ω-point" requires. The six accepted proof steps are all in the docstring.
Only lean is changed in the copied node, and its statement field is extracted verbatim
from the theorem keyword to the assignment token.

## Validation

Every compiler invocation used the prescribed scompile.py wrapper, against the published
live server build. Final compile and deliver2.py dry-run results are recorded below.

Final scompile.py check: clean sandbox compile (4.2 s) and library-module compile (3.2 s),
with no errors or warnings. The deliver2.py --no-push dry run reported
`OK (dry run): commit 12d1af5c6c0 passes the preflight and compiles; nothing pushed`.
