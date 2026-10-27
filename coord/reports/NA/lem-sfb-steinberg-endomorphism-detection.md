## Worker report

The module `Sheaf.AlgebraicGeometry.SteinbergEndomorphismDetection` states
`AlgebraicGeometry.exists_steinberg_endomorphism_detection`, with its entire proof
`sorry`. Its real Prop-valued helper `HasSteinbergEndomorphismDetection` unfolds
exactly the conclusion of this node. No representation, coaction, subgroup scheme,
or canonical action is redefined, and no theorem is proved.

Hypothesis and clause correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The F-group scheme is `(S : Over (Spec (.of F))) [GrpObj S]`.
- Semisimplicity is `hS : IsSemisimpleGroupScheme S`. Reading its definition gives
  smoothness, connectedness, affineness, locally finite type plus quasi-compactness
  (finite type), and triviality of every smooth connected solvable normal closed
  subgroup. Its existing recursive scheme-derived-series predicate gives solvability.
- Simple connectedness is the entire `hsc` binder: for every semisimple group scheme
  S' and multiplicative scheme morphism f, scheme-surjectivity and finite central
  kernel imply `IsIso f`. Finite is `IsFinite (GrpObj.ker f).hom`, equivalently
  finite-dimensional coordinate algebra over F. The centrality equation quantifies
  over every commutative F-algebra A and every kernel and S' point over A.
- The quantified finite-dimensional rational U and existential E are the existing
  `EquivariantCoherent.Representation F S`. This is `RationalModule` over the
  canonical coordinate Hopf algebra, with a `ModuleCat F` space, `Module.Finite`,
  actual linear coaction, and counitality and coassociativity proofs. All definitions
  and the full recorded interfaces were read. This is exactly the notion in the node.
- Nonzero invariant x is `x ≠ 0` and `U.coaction x = x ⊗ₜ[F] 1`.
- E is nonzero by `Nontrivial E.space`; finiteness and rationality are bundled in E.
- The desired F-linear map is `φ : U.space →ₗ[F] Module.End F E.space`.
  Detection is `φ x ≠ 0`.
- Equivariance for the specified conjugation action is the displayed coaction
  identity for evaluation `TensorProduct.lift φ : U ⊗ E →ₗ[F] E`.
  `HopfAction.tensorCoefficients` multiplies the coordinate coefficients of the U
  and E coactions, giving precisely the diagonal coaction. Thus the equation says
  ev(su,se)=s ev(u,e) after every scalar extension. Invertibility of s on E makes
  this equivalent to φ(su)=s φ(u) s⁻¹. This states the canonical conjugation action,
  without quantifying over an arbitrary action or relying only on F-points.
- The elementwise equality of the conjugation-fixed endomorphism space with F id
  is `∀ a, IsRepresentationMap E E a ↔ ∃ c : F, a = c • LinearMap.id`.
  The existing `IsRepresentationMap` is the coaction-commuting identity. For the
  conjugation action this is exactly being fixed: after every scalar extension,
  a commutes with every s iff s a s⁻¹=a. Both directions of the scalar-line equality
  are present; this is not just an upper bound on invariants.
- No characteristic assumption occurs; characteristic zero and all positive
  characteristics are included. Simple connectedness and semisimplicity include S=1.

The affine instance needed to form coordinate comodules is supplied explicitly by
`hS.2.2.1` when the theorem applies its conclusion helper. No separate affineness
assumption and no statement-local let/have/instance or hidden choice is used.
This helper belongs to the node's own conclusion and is recorded in `lean.declarations`;
it introduces no independent mathematical notion needing a new DAG node.

Dependencies used:

- `Field`, Mathlib.Algebra.Field.Defs; `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic (the algebraic-closure node's exact match).
- `CategoryTheory.GrpObj`, `IsMonHom`, `GrpObj.ker`, `GrpObj.kerι`,
  Mathlib.CategoryTheory.Monoidal.Grp and the recorded
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs interface. Its full docstring
  identifies exactly the group-scheme convention, finite groups and kernels.
- `AlgebraicGeometry.IsSemisimpleGroupScheme`,
  Sheaf.AlgebraicGeometry.GroupScheme.Semisimple.
- `AlgebraicGeometry.EquivariantCoherent.Representation`, `RationalModule`,
  `coordinateHopf`, `IsRepresentationMap`,
  Sheaf.AlgebraicGeometry.RationalRepresentationGZero.
- `HopfAction.tensorCoefficients`, `Coassociative`, `Counital`,
  Sheaf.RingTheory.HopfActionModuleData, publicly reexported by the rational module.

The last three owning definition nodes are added to stmt_deps as existing landed
nodes. Their recorded definitions are reused without modification. There are no new
nodes, dependency repairs, or changes to the mathematical statement.

Proof-dependency imports: `Sheaf.AlgebraicGeometry.RhoSectionModules` is imported
privately because its node is already stated. The other three proof dependencies
(eventual detection, self-duality and the invariant line) have no recorded Lean
statements at the time of writing, so their modules cannot yet be imported. Their
complete five-step assembly, tensor-Hom formula, basis inverse, common-index choice
and invariant-line argument are retained in the theorem docstring for stage 3.

Edge cases checked before drafting: U=0 admits no nonzero x, so the assertion is
vacuous; x=0 is explicitly excluded; E=0 is explicitly excluded. For S=1 take E=F
with trivial action, and a linear functional on U nonzero at x, multiplied by id.
This has exactly scalar endomorphisms. For U=F with trivial action one may likewise
take E=F. Characteristic 2 introduces no division by 2 into this statement, and no
positive-characteristic self-duality at arbitrary weights is asserted. Nonreduced
central kernels are allowed by the scheme-theoretic kernel and all-algebra test.
Finite-dimensional spaces use the existing single-universe rational-module convention;
a finite basis transports any finite-dimensional space to F^n, so this loses no
finite-dimensional representation or case. Test algebras range over the field's
universe, including the coordinate algebra and tensor products; the universal point
detects the coaction identities and hence arbitrary scalar extensions as well.

Searches made for an existing statement:

- msearch.py leanfinder, query “A nonzero invariant vector in a finite dimensional
  rational representation of a semisimple simply connected algebraic group is
  detected in an endomorphism representation with scalar invariants”: eight hits,
  including FDRep.simple_iff_end_is_rank_one and finite-group character lemmas;
  none constructs the required rational algebraic-group representation.
- msearch.py loogle, `HopfAlgebra, Comodule`: no hits (unknown Comodule identifier).
- msearch.py grep, `Steinberg|[Cc]onjugation.*[Cc]oaction|[Ss]emisimple.*[Gg]roup`:
  three unrelated semisimple-module hits; no detection or conjugation-coaction API.
- msearch.py leansearch, “Steinberg rational representation semisimple simply
  connected invariant vector endomorphism detection”: eight hits concerning
  abstract-group invariants and semisimple linear operators; no detection theorem.
- rg in lean/WeilConjectures for the item id, Steinberg, coaction and semisimple
  group schemes: no matching detection declaration. Steinberg results there concern
  Lang--Steinberg for semilinear Frobenius, which is a different theorem.
- rg in lean/Sheaf/AlgebraicGeometry for RationalModule, NaturalRepresentation,
  coaction, IsSemisimpleGroupScheme and endomorphism/conjugation: located the exact
  existing rational-module, comodule dictionary and semisimplicity interfaces used
  above; no detection theorem. `dag/lean_names_upstream.json` likewise has only the
  unrelated Lang--Steinberg attachment, not this statement.

Source read: Alper's current HTML at
https://arxiv.org/html/1005.2398v3#S9.SS7, Lemmas 9.7.2, 9.7.4, Remark 9.7.3 and
Theorem 9.7.5; its endomorphism construction matches the node. The existing nonzero
qualification and field specialization in the node are preserved. The current
blueprint file `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`
was read: this is the supporting Haboush input along the node's inherited
alteration/moduli chain, not a change to a unit statement.

Validation: scompile.py compiled the sandbox and final named library module cleanly
on the server (29.1 s and 2.0 s); only the authorized wrappers were used. The first
probe exposed missing inferred affine/Hopf instances; packaging the actual conclusion
as a Prop helper and applying it with hS's affine proof fixed that interface without
adding assumptions. Every variable and universe is explicitly bound.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
