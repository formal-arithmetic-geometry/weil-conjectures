## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveGITSemistableReplacement` states
`AlgebraicGeometry.exists_projective_git_semistable_replacement`; its only proof is
`sorry`. No definitions, new nodes, dependency repairs or statement corrections are needed.
The complete six-step proof from the DAG is in the theorem docstring.

Source read: Morrison, *GIT Constructions of Moduli Spaces of Stable Curves and Maps*,
arXiv:0810.2340, §3.3, proof of Corollary 11(2), printed p.17, online PDF,
https://arxiv.org/pdf/0810.2340 (PDF page 17). The cited argument extends the generic
quotient point using projectivity, then obtains an integral semistable point whose
new generic fibre is in the original orbit. The supplied DAG gives its detailed
arbitrary-characteristic expansion, including invariant closed images and trait selection.

Hypotheses and clauses, in node order:

- Any field k: `(k : Type u) [Field k]`; no characteristic instance.
- r ≥ 2 and G = PGL: `(r : ℕ) (hr : 2 ≤ r)`, the supplied group scheme `G`,
  quotient map `π` and roots inclusion `j`, and
  `hG : ProjectiveMatrixCentralCover.Presentation k r hr G π j`.
  This recorded presentation identifies PGL by the fpqc scalar-quotient universal
  property on every test scheme. It is a supplied presentation of the specified group,
  not a stronger assumption on that group and not a choice from an existence theorem.
- Projective finite-type k-scheme Z: `Z : Over (Spec (.of k))`,
  `[IsHProjective Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]`.
  These are the recorded projective and finite-type conventions; they permit nonreduced Z.
- Algebraic G-action: `action : ModObj G.X Z`, the existing internal action structure.
- Ample G-linearized invertible A: `A : Z.left.Modules`, `[A.IsInvertible]`,
  `hA : Scheme.Modules.IsAmple Z.left A`, and
  `D : GroupSchemeLinearization.Linearization action A`.
  Its naturality and cocycles are tested on every scheme, including nonreduced tests.
- Geometric semistability convention: `U : Z.left.Opens` and `hU` characterize its
  geometric points by `D.IsSemistable Ω x`, for every algebraically closed Ω/k.
  This is exactly the invariant positive-power section definition in the recorded
  Hilbert–Plücker dependency, using its general group-scheme linearization.
  Supplying the open characterized by its points identifies the node's specified
  `Z^{ss}(A)`; it does not assume all points are stable.
- DVR k-algebra R and fraction field K: `[CommRing R] [IsDomain R]`,
  `[IsDiscreteValuationRing R] [Algebra k R]`, `[Field K] [Algebra R K]`,
  `[IsFractionRing R K] [Algebra k K] [IsScalarTower k R K]`.
  The tower merely expresses the induced k-algebra structure on the specified fraction field.
- Generic semistable point z: `z : PGLLinearization.fieldTest k K ⟶ Z` and
  `hz : z.left (IsLocalRing.closedPoint K) ∈ U`.
  Spec K has one point; this is equivalent to the unique factorization into the open U.
- Finite fraction-field extension K'/K: existential `K'`, its `Field` and `Algebra K K'`
  instances, and `Module.Finite K K'`; its k-structure has `IsScalarTower k K K'`.
  A field algebra map is automatically injective; inseparable extensions are permitted.
- Replacement DVR R' and local injective k-algebra map: `R' : Subalgebra k K'`,
  `IsDiscreteValuationRing R'`, `IsFractionRing R' K'`, `φ : R →ₐ[k] R'`,
  `Function.Injective φ` and `IsLocalHom φ`.
  A domain structure on R' is inherited from its inclusion in K'. Identifying a DVR
  with its image under its injective fraction map gives exactly this subalgebra form.
  Conversely every displayed subalgebra is an actual DVR with the required fraction field.
- The inclusions induce the stated field extension:
  `R'.val.comp φ = (IsScalarTower.toAlgHom k K K').comp (IsScalarTower.toAlgHom k R K)`.
  This expresses the compatibility implicit in the phrase 'extension of fraction fields'.
- Element h ∈ G(K'): `h : PGLLinearization.fieldTest k K' ⟶ G.X`.
  This uses actual group-scheme points, without requiring a lift to a matrix or SL point.
- Integral semistable point b: `b : specAlgOver (k := k) R' ⟶ Z` and
  `∀ p : Spec (.of R'), b.left p ∈ U`. As U is open, this is equivalent to the
  unique morphism Spec R' → U; no arbitrary comparison map is supplied.
- Generic equality b|K' = h · z_K':
  `specAlgOverMap R'.val ≫ b = GroupSchemeLinearization.act action ... h
  (specAlgOverMap (IsScalarTower.toAlgHom k K K') ≫ z)`.
  Both sides are actual morphisms over k, not just their images or orbits.
- Closed point to closed point:
  `(Spec.map (CommRingCat.ofHom φ.toRingHom)) (IsLocalRing.closedPoint R') =
  IsLocalRing.closedPoint R`. This is the node's explicit clause as well as the
  geometric meaning of locality of φ.
- No characteristic-zero, linear-reductivity, stability, excellence, completeness,
  finite-module condition on R'/R, or separability condition is imposed.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `AlgebraicGeometry.IsHProjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` / `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`, with `IsDomain`.
- `Sheaf.AlgebraicGeometry.HilbertPluckerPGLLinearization` exposes its recorded
  `HilbertPlucker.Presentation`, including the PGL presentation, `pgl_line` and
  `semistable_points`. It publicly imports the interfaces used here:
  `Sheaf.AlgebraicGeometry.GroupSchemeLinearization` (`act`, `Linearization`,
  `Linearization.IsSemistable`), `Sheaf.AlgebraicGeometry.ProjectiveMatrixCentralCover`
  (`Presentation`), and `Sheaf.AlgebraicGeometry.PGLLinearizedPolarization` (`fieldTest`).
  No Hilbert-scheme datum or Hilbert polynomial is imposed on arbitrary Z.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.Ample`: `AlgebraicGeometry.Scheme.Modules.IsAmple`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Scheme.Opens`.
- Existing canonical affine helpers from `WeilConjectures.AlgebraicGeometry.GenericQuotient`:
  `AlgebraicGeometry.specAlgOver` and `AlgebraicGeometry.specAlgOverMap`, read in full.
  `specAlgOver` is definitionally the same object as `PGLLinearization.fieldTest` for fields.
- Plain proof imports preserve every currently recorded proof dependency module:
  `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper` (`hProjective_properness`),
  `Mathlib.AlgebraicGeometry.ValuativeCriterion` (`UniversallyClosed.eq_valuativeCriterion`),
  `Mathlib.RingTheory.Jacobson.Ring` (`finite_of_finite_type_of_isJacobsonRing`), and
  `Sheaf.RingTheory.DiscreteValuationRing.FinitelyGeneratedExtension`
  (`IsLocalRing.exists_discreteValuationSubring_of_fg_extension`). The other three
  proof dependencies currently have no Lean record; their arguments remain in the docstring.

Edge cases checked by reading the signature and definitions: r = 2 is included; characteristics
which divide r are included (no reduced central kernel required); arbitrary finite inseparable
extensions are included; the action may be trivial and stabilizers positive-dimensional;
nonreduced Z is allowed. If Z or U is empty, no z satisfying hz exists, so the hypothesis correctly
makes this case vacuous. DVR excludes fields, as in the node. R'/R need not be finite as a module.
The trivial fraction-field extension and R' = R (up to its image) are permitted. All objects use
one arbitrary explicit universe u, the size convention of the recorded action and semistability
interfaces; none of the test-object universes is independently smaller than the base field.

Searches actually run:

- `msearch.py ... leanfinder`: 'Semistable replacement for a projective scheme with a linearized
  PGL action over a discrete valuation ring after finite field extension and change of coordinates'.
  Eight results, notably `Proj.valuativeCriterion_existence` and
  `WeierstrassCurve.exists_isMinimal`; none states group-theoretic semistable replacement.
- `msearch.py ... loogle`: 'IsDiscreteValuationRing, IsLocalHom, IsFractionRing': zero hits.
- `msearch.py ... grep`: 'semistable|Semistable|Linearization', subdirectory AlgebraicGeometry:
  zero Mathlib hits.
- `msearch.py ... leansearch`: 'projective geometric invariant theory semistable replacement
  over a discrete valuation ring': eight hits, concerning DVRs and Weierstrass minimal models;
  none gives this statement.
- `rg -n 'semistable|Semistable|Linearization|PGL|ProjectiveMatrix'` on the project's
  `lean/Sheaf/AlgebraicGeometry` and `lean/WeilConjectures/AlgebraicGeometry` found the
  general group-scheme linearization, PGL presentation, and Hilbert–Plücker module used here.
- `rg -n 'semistable.replacement|semistable_replacement|lem-sfb-projective-git-semistable-replacement'`
  on `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` returned no match.
- `rg` for canonical affine Over maps located upstream `GenericQuotient.specAlgOverMap`;
  it is reused rather than defining any new Spec transport.

Validation: scompile.py compiled the module against the published live library, both sandbox
and final module paths, with no errors or warnings. The wrapper also compiled the upstream
GenericQuotient overlay and its prerequisites. No statement dispute or node fault found.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
