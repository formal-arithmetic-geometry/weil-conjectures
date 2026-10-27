## Worker report

The module `Sheaf.AlgebraicGeometry.HenselianClopenGroupHomApproximation` states
`AlgebraicGeometry.henselian_clopen_group_hom_approximation`, with its proof postponed
by `sorry`. The declaration docstring includes all thirteen steps of the accepted split,
including the nonunital corner inverse, actual relation-membership witnesses, all three
operation identities and order-one approximation. No definitions, new nodes, dependency
repairs or statement corrections are needed. The item changes only in `lean`.

Hypothesis and conclusion correspondence:

- The commutative henselian local ring is `{A : Type u} [CommRing A]
  [HenselianLocalRing A]`. The latter class includes `IsLocalRing A`, rather than
  imposing a second unrelated local structure. The G-ring condition is `hA : IsGRing A`;
  that recorded definition includes Noetherianity.
- The maximal ideal is `IsLocalRing.maximalIdeal A`. Its completion is exactly
  `AdicCompletion (IsLocalRing.maximalIdeal A) A`, with the canonical algebra structure
  and `algebraMap A ...`. The residue field is `A ⧸ IsLocalRing.maximalIdeal A`,
  definitionally `IsLocalRing.ResidueField A`. The canonical completion projection is
  `(AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal A)).toRingHom`.
- The coordinate algebras are `P Q : Type u` with `CommRing`, `Algebra A`, and
  `Algebra.FinitePresentation A` instances for each. All rings and spectra live in a
  common universe `u`, which is arbitrary. There is no finiteness assumption on the
  cardinality of the underlying rings.
- The two affine A-schemes are `((Spec (.of P)).asOver (Spec (.of A)))` and the analogous
  expression for `Q`. Their structure maps are Spec of the corresponding algebra maps.
  Each has a separately quantified `GrpObj` structure, precisely multiplication,
  identity and inverse with the group diagrams. The ring commutativity does not assert
  commutativity of these group laws.
- The scalar-extension functor is
  `Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A ...)))`.
  Its objects are the chosen fibre products; their group structures come from the
  existing product-preserving-functor instances enabled by `CategoryTheory.Obj`.
  These are the base changes of the GIVEN group structures, not independently
  quantified structures on the completions.
- `v` is an Over-morphism between those scalar extensions. `[IsMonHom v]` preserves
  multiplication and identity. Inverse preservation follows for group objects
  (`CategoryTheory.GrpObj.inv_hom`), so it is exactly a group homomorphism.
  `[IsOpenImmersion v.left] [IsClosedImmersion v.left]` give both immersion conditions
  on its underlying scheme morphism, not merely on the underlying topological map.
- The existentially quantified `w` is an A-morphism between the original affine
  schemes. The conjuncts `IsMonHom w`, `IsOpenImmersion w.left` and
  `IsClosedImmersion w.left` give exactly the three requested properties.
- In the final equality both `w` extended to the completion and `v` are pulled back
  along Spec of `AdicCompletion.evalOneₐ`. Thus both sides have literally the same
  source and target: the iterated fibre products over `Spec (A/m)`. The identity
  `AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk` says that the composite ring map
  `A → Ahat → A/m` is the quotient map. The canonical pullback associators therefore
  identify the left side with `w_k` and the right with `v_k`. This expresses exactly
  the equality under the canonical residue identification, without selecting any
  arbitrary residue-field isomorphism. The order-one completion theorem identifies
  its kernel with the extended maximal ideal since the G-ring is Noetherian.
- No flatness, smoothness, commutative group law, diagonalizability or equality over
  the completion occurs among the hypotheses or conclusions.

Dependency declarations read and used:

- `WeilConjectures.Mathlib.RingTheory.Henselian`: `HenselianLocalRing` (from its
  Mathlib public import); its full class extends `IsLocalRing`. This is the relevant
  component of def-weil-pbc-henselian-terminology, not its strictly henselian class.
- `WeilConjectures.RingTheory.GRing`: `IsGRing` (including its full local-completion
  definition and Noetherian conjunct).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` is the quotient of
  the local stalk by its maximal ideal. Here the ring-local specialization uses its
  underlying `IsLocalRing.ResidueField`, as the node explicitly writes `k=A/m`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`, its
  canonical algebra structure, `AdicCompletion.evalOneₐ`, and the composite identity.
  These are publicly supplied by the recorded G-ring module.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`; publicly supplied by the
  geometric imports. `Mathlib.AlgebraicGeometry.Over`: `Scheme.asOver`.
  `Mathlib.AlgebraicGeometry.Group.Affine`: the canonical `specOverSpec` instance
  relating each algebra to its affine scheme over `Spec A`. The first compile
  diagnosed its missing import; adding the owning module fixed that interface.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation` with its
  finite-polynomial-quotient definition.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, projections
  and universal property, used through `Over.pullback` and the Scheme pullback instance
  from `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.CategoryTheory.Monoidal.Grp`, `.Mon` and `.Cartesian.Over`: `GrpObj`,
  `IsMonHom`, functorial group-object scalar extension and the cartesian monoidal
  structure on Over. These are existing Mathlib definitions. The node already spells
  out these group diagrams, so no replacement definition or new group-scheme notion
  is introduced.

Proof-only imports follow every recorded proof dependency: affine spectra and
products (`Mathlib.AlgebraicGeometry.Pullbacks`), clopen/idempotent correspondence
(`Mathlib.RingTheory.Spectrum.Prime.Topology`), affine basic-open localization
(`Mathlib.AlgebraicGeometry.ResidueField`, publicly importing AffineScheme),
multivariable polynomials (`Mathlib.Algebra.MvPolynomial.Basic`), algebra homomorphisms
and quotients (`Mathlib.Algebra.Algebra.Hom`, `Mathlib.RingTheory.Ideal.Quotient.Operations`),
`WeilConjectures.RingTheory.HenselianPairApproximation.henselian_pair_approximation`
(the declaration is at the root namespace), and completion modulo powers
(`Mathlib.RingTheory.AdicCompletion.Completeness`). The recorded declarations were
read in the read-only source; no interface mismatch was found.

Edge cases checked before writing: if `A` is a field, `m=0` and the completion and
residue maps recover the expected situation. Identity maps, trivial groups, and
idempotent `e=1` are included. The zero ring is not a local ring in Mathlib's convention,
which agrees with the usual local-ring convention in the source. Empty coordinate
presentations and empty relation lists cause no restriction, because the statement
uses `Algebra.FinitePresentation` rather than a nonempty generator list. No property
requires the affine groups to be smooth, reduced or flat. Complete `A` does not cause
an extra conclusion of equality with the given map, which is correctly absent.

Searches for existing declarations:

- msearch leanfinder: `Henselian approximation of a clopen affine group scheme
  homomorphism from the completion preserving the special fibre`: eight hits, including
  `Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq`,
  `IsAdicComplete.henselianRing`, `IsAdicComplete.liftAlgHom`; these concern smooth
  lifting or completion and do not state this assertion with its group and clopen
  certificates.
- msearch loogle: `HenselianLocalRing, AlgHom`: only `HenselianLocalRing.TFAE`,
  not an approximation theorem for the given group morphism.
- msearch grep: `approximation|henselian|clopen` in `AlgebraicGeometry/Group`: zero hits.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for henselian/approximation and clopen
  group maps found existing general henselian algebra-map approximation and clopen
  restriction modules, but no theorem approximating the given clopen group map.
  Existing `HenselianApproximationAlgHom` alone cannot express the conclusion,
  because the inverse-corner and group-law polynomial certificates are also required.
- Exact blueprint-id grep in `lean/WeilConjectures` and full declaration-name search
  in `dag/lean_names_upstream.json`, Mathlib, WeilConjectures and Sheaf: no matches.

No STATEMENT-DISPUTED issue is identified. The source Tag 0AH5, its henselian-pair
hypotheses and all thirteen accepted finite-certificate steps were read.

## Second reading by NX

The dispatcher requires this worker to act alone and forbids starting agents; the
maintainer performs the independent review. This section records a separate self-check,
not an independent review by another person or agent.

Re-read the original node and the final signature: henselian locality and `IsGRing`
are both present; completion and its A-algebra map are the canonical ones; the two
coordinate algebras are separately finitely presented; their given group laws use
`GrpObj`, without `IsCommMonObj`; the completion group structures are the functorial
images of those laws; `v` is an `IsMonHom` and has both immersion instances. The
existential `w` has exactly the analogous three properties. The final equality is
after the residue pullback, comparing the same iterated products on each side.
`evalOneₐ_comp_algebraMap_eq_mk` verifies that this really is the requested special
fibre equality. There is no completion equality, no uniqueness assertion and no added
flatness hypothesis. No mismatch or statement change was found. `autoImplicit false`
checks that every variable and universe is explicitly bound.

Validation: the final module (including `autoImplicit false` and the affine-group
instance import) compiled successfully using the prescribed `scompile.py`, both as
sandbox and library modules, with exit code 0 and no warnings. The Lean source has
no lines exceeding 100 characters. The declaration record copies its final signature
verbatim. Dry run and delivery are performed by `deliver2.py`.
