## Worker report

The module `Sheaf.Paper.ResidueCompatiblePullbackFrobenius` states the item in the
existing rational and common-stage constructible categories. It constructs the
specified comparison components from actual pullback compositors; no definition
has postponed data. The theorem statements are deliberately unproved (stage 2).
All 26 public declarations are listed in the node's `lean.declarations`. The main
recorded signature is verbatim from `residueCompatiblePullbackFrobenius`; the
remaining clauses are separate named theorems in that same module, not omitted
from the delivery. No original statement or proof has been changed. Two landed
notion nodes were added to `stmt_deps` for the actual geometric base-change map
and the canonical shifts used in the triangulated assertion.

Hypothesis and clause correspondence:

- Finite base field, closure and characteristic: `D : FiniteFieldDatum.{u}`.
  The prime and unequal characteristic are `[Fact l.Prime]` and `hl : l ≠ D.p`.
  Finite coefficients use `E`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]`; closed coefficients use `Ω` with
  `[IsAlgClosure ℚ_[l] Ω]`. These are the recorded coefficient conventions.
- Models and the base map: `W₀ X₀ : Over (Spec (.of D.k₀))`,
  `[LocallyOfFiniteType W₀.hom]`, `[QuasiCompact W₀.hom]`, and the analogous
  instances for X₀ mean finite type. The main theorem binds
  `[IsSeparated W₀.hom] [IsSeparated X₀.hom]` and `f₀ : W₀ ⟶ X₀`.
  `zlFiberMap D f₀` is the actual base change; Rational.pull and Common.pull
  abbreviate the dependency's actual derived inverse image, including its units.
- Frobenius exact autoequivalence, including semilinear automorphisms:
  `frobenius_exact` asserts `IsEquivalence`, `IsTriangulated` with the recorded
  canonical shifts, and an iff on each of the two standard classes at every
  integer bound, at both coefficient levels. It uses scheme automorphisms, not
  an assumption that geometric Frobenius is a k-morphism.
- Every m ≥ 1: `localPositivePower ... n` means m = n+1.
  `Rational.Pullback` and `Common.Pullback` contain the scheme commutation for
  every n, natural isomorphisms `alpha n`, and `normalization` fixing every
  component to `alphaComponent`. That definition is inverse compositor, equality
  of the actual composite scheme maps, then compositor in the other order.
- Induced Weil functor: `IsoAlgebra.mapOfNatIso (P.alpha 0)` (and Q) is the
  existing functor on fixed pairs. Its structure is alpha followed by pullback of
  theta. `Pullback.iterate` is the asserted equality with the existing normalized
  `localWeilIterate` / `localQbarWeilIterate` for every positive exponent.
- Closed z and x=f₀(z): the main theorem quantifies the closed-point subtype z
  and `hx : f₀.left z.val ∈ closedPoints X₀.left`. The hypothesis is
  `IsIso (f₀.left.residueFieldMap z.val)`, the actual contravariant residue map,
  not existence of an unrelated isomorphism. Because f₀ is over k₀ its residue
  map is over k₀. `Local.degree_eq` identifies the two recorded residue degrees.
- Embeddings: `ιz`, `ιx` are the actual residue embeddings into D.k;
  `hz`, `hιx` say they are over k₀; the compatibility equality composes ιz with
  the actual residue map to give ιx. `Local.point_eq` is precisely zbar f=xbar.
  `Local.return_x` uses the same exponent as the source return, so both sides
  use the same point Frobenius, even when the common degree is greater than one.
- Specified e and c: `pointComponent` is the inverse dependency compositor,
  followed only by the point equality. `fibreComponent` is its image under
  `pointRationalFibre` / `pointQbarFibre`. The two `*_point_naturality` theorems
  explicitly assert naturality at arbitrary constructible arrows, before fibres.
  Thus c is a specified natural isomorphism, rather than an existential stalk map.
- Three separate factors: `Local.transport` is the square for I^[r];
  `Local.return_compositor` is Rz, point pullback of alpha_r, then e at G_X^rK,
  equal to H(e) then Rx; `Local.weil_map` is the naturality square at theta^[r].
  `Local.derived` states Fz then c = c then Fx as derived morphisms.
  `Local.cohomology` applies the actual coefficient cohomology functor in every
  integer degree. All these fields are stated independently at both coefficient
  levels. `rational_heart` and `common_heart` restrict the actual pullback to the
  recorded constructible hearts; degree zero of the same specified fibre
  comparison gives the canonical stalk identification with the equivariance
  already stated by `Local.cohomology`.
- Locally closed immersion: `immersion_residue` binds `[IsImmersion f₀.left]`.
  Mathlib's `IsImmersion.isImmersion_iff_exists` is exactly a closed immersion
  followed by an open immersion. Its conclusions are closed image, isomorphism
  of the actual residue map, and `Nat.card` equal to q raised to the common
  residue degree for BOTH fields. It does not assume an arbitrary open embedding
  preserves points closed only in its subspace.
- Finite coefficient extension: `composition_scalar` quantifies arbitrary finite
  fields E,L and an algebra map ι. It gives the scalar square for the specified
  rational compositor and canonical `rationalPullbackScalarComparison`.
  Inverting and composing this square gives the same square for alpha, e and R;
  naturality of the same comparison covers maps induced by theta^[r].
  `transport_scalar` explicitly gives the remaining I^[r] square with the
  canonical point-fibre scalar isomorphism. Consequently their composites and
  every cohomology map commute with extension. The Common definitions and Local
  theorem use the recorded finite-representative common-stage maps, so the maps
  are also stated at Ω and not only over finite coefficients.
- Finite diagram descent: `finite_diagram_descent` quantifies a finite quiver I
  (finite vertices and each edge set), a functor from its path category, and any
  finite family of parallel path equations. It produces ONE coefficient index L,
  a rational Weil functor A at L, object isomorphisms to the actual
  `sfWeilStageObject`, equality of all represented arrows under conjugation,
  and all the prescribed path equations at L. Each A-object already has an
  invertible Weil structure, so its two inverse equations hold at that stage.
  This handles cycles: the path category itself need not have finitely many
  morphisms. No stable lattice hypothesis occurs anywhere.

Dependency declarations actually reused:

- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`,
  `sfCommonStageWeilComplex`, `sfWeilFrobeniusPullback`,
  `sfCommonStageWeilFrobeniusPullback`, `sfWeilStageObject`, prime units.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `commonStageDerivedPullback`, `rationalPullbackScalarComparison`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: the common-stage category,
  coefficient indices, finite coefficient fields and `inclusion` on actual arrows.
- `Sheaf.Paper.SfConstructibleHeart`: both standard classes and both heart properties.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPullbackComposition`,
  `localQbarPullbackComposition` (rationalized integral compositor),
  `localPositivePower`, all iterate, transport, return, local closed Frobenius
  and coefficient cohomology constructions, closed points and residue degrees.
- `Sheaf.Paper.WeilIndSheafCategory`: `zlFiberMap`; this is a landed notion node.
- `Sheaf.Paper.FieldWeilShriekShiftData`: `fieldWeilFrobeniusShift` and
  `fieldCommonWeilFrobeniusShift`; this is the other added landed notion node.
- Mathlib `Scheme.residueField`, `Scheme.Hom.residueFieldMap`, `IsImmersion`,
  `IsClosedImmersion`, `IsOpenImmersion`, `Paths`, `IsoAlgebra.mapOfNatIso`,
  `IsoAlgebra.forget`, `Functor.IsEquivalence`, `Functor.IsTriangulated`.
- The node's stated proof-dependency modules are plain imports, with their named
  proof ingredients described in each postponed theorem's proof docstring.

Edge cases checked: empty geometric schemes and no closed points leave the
pullback and natural comparisons meaningful; residue degree one uses power index
zero, not an identity Frobenius; residue maps of higher degree are excluded by
exactly the actual-isomorphism hypothesis; unrelated residue embeddings do not
satisfy the compatibility hypothesis. Identity f and open/closed immersions are
included. The local operator remains a derived morphism for complexes outside the
heart and for nonzero cohomological degrees. The empty graph and zero relations
are permitted, as are cycles and repeated paths. Finite quiver morphism sets do
not impose finiteness of paths. Semilinear Frobenius is never fed to a theorem
requiring a k-linear morphism.

Searches performed before writing:

- `msearch.py ... leanfinder "Derived pullback of Weil pairs intertwines local
  Frobenius at closed points with isomorphic residue fields"`: eight results
  concerning scheme residue fields; no derived Frobenius theorem of this scope.
- `msearch.py ... loogle "TopCat.Presheaf.stalkPullbackIso,
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso"`: no result (second name is
  project/upstream rather than Mathlib). Read the actual upstream fixed-pair API.
- `msearch.py ... grep "localFrobenius|WeilComplex|stalkPullbackIso"`: Mathlib
  `Topology/Sheaves/Stalks.lean` has the ordinary presheaf stalk isomorphism;
  it does not supply a derived three-factor comparison.
- `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  residue-compatible pullback, Frobenius, Weil pairs, compositor and scalar maps:
  found the reused modules above. The old upstream derived-Weil-sheaf convention
  is not the fixed-pair constructible category required here. The existing
  immersion/extension-by-zero statements only address their respective functors
  and degree-zero comparisons, not this general morphism and all three factors.
- Searched DAG records and read all statement dependencies' complete recorded
  signatures. Checked the transitive DAG dependencies before considering reuse
  of `zlWeilStageSquare`: its owning theorem depends on this item. It is not
  imported. Descent instead uses the already recorded stage object and forgetful
  functors, so adds no duplicate definition and no dependency cycle.

No statement correction, disputed statement, new node, or dependency repair is
needed. Validation uses only the prescribed scompile.py and deliver2.py wrappers;
no project-wide build and no direct changes to the shared checkout.

## Second reading by Q52

Independent second reading (maintainer reviewer NT-cc, 2026-10-25). It replaces the
author's self-check delivered at 54c33f7f, which was not an independent reading (H11).
The Lean was read against the node statement, its eleven proof steps and the
declarations of every statement dependency (live side clone). The Lean and the node
record are unchanged.

Node clauses and their Lean rendering:
- k0 = F_q, k, l ≠ p, E finite over Q_l, Qlb: `D : FiniteFieldDatum.{u}`, `[Fact l.Prime]`,
  `hl : l ≠ D.p`, `E` with `FiniteDimensional ℚ_[l] E`, `Ω` with `IsAlgClosure ℚ_[l] Ω`.
  E, Ω : Type u is the universe of def-weil-local-frobenius-trace (localWeilIterate,
  localQbar* take `Ω : Type u`); not a new restriction. Exact.
- f0 : W0 → X0 separated finite type, f its base change: `Over (Spec k0)`,
  `LocallyOfFiniteType`+`QuasiCompact`, `[IsSeparated]` in the main theorem;
  `zlFiberMap D f₀ = (Over.pullback (Spec k → Spec k0)).map f₀).left`
  (def-zl-weil-ind-sheaf-category, now cited). Exact.
- G_T exact autoequivalences preserving standard t-structures, also semilinear:
  `frobenius_exact`: IsEquivalence, IsTriangulated (CommShift = the instance
  `fieldWeilFrobeniusShift` / `fieldCommonWeilFrobeniusShift` of
  def-zl-field-weil-shriek-shift-data, i.e. the canonical pullback shift, not a free
  one; sfWeilFrobeniusPullback is a plain def so no other instance applies), and an
  iff on both standard classes at every bound, at E and Ω. Arbitrary T0 of finite
  type. Exact.
- α_m = d_{f,g_X^m}^{-1} d_{g_W^m,f}: `Pullback.alpha n` pinned componentwise by
  `normalization` to `alphaComponent` = (compositor (g_W^{n+1}, f))⁻¹ ≫ eqToIso(commutes)
  ≫ compositor (f, g_X^{n+1}); `localPullbackComposition h k : P(h≫k) ≅ P_h P_k`, so the
  direction is G_W^m Lf^* → Lf^* G_X^m. All m ≥ 1 via n+1. Data pinned → the ∃ P, Q
  is a determined package.
- θ_f = Lf^*(θ) α_1 and (θ_f)^[m] = Lf^*(θ^[m]) α_m: `IsoAlgebra.mapOfNatIso (alpha 0)`
  has str = α.app ≪≫ L.mapIso θ (mapOfNatIso_obj_str); `iterate` is the equation with
  the recorded `localWeilIterate` / `localQbarWeilIterate`. Exact.
- closed z, x = f0 z, actual residue map iso, r: subtype z, `hx`, `IsIso
  (f₀.left.residueFieldMap z.val)` (κ(f z) → κ(z)); `Local.degree_eq`. Exact.
- compatible embeddings, x̄ = f z̄: ιz, ιx over k0 (`hz`, `hιx`), `ιz ∘ residueFieldMap = ιx`;
  `Local.point_eq`, `Local.return_x` (same exponent r). Exact.
- c_K = Fib(inverse compositor): `pointComponent` (compositor (z̄, f))⁻¹ ≫ eqToIso,
  `fibreComponent` its image under `pointRationalFibre` / `pointQbarFibre`;
  naturality in arbitrary derived arrows: `rational_point_naturality`,
  `common_point_naturality`. Exact.
- three factors and c_K F_z = F_x c_K: `transport` (I_A ≫ V(H e) = c ≫ I_B),
  `return_compositor` (R_z ≫ P_z α_r ≫ e_{G^rK} = H e ≫ R_x), `weil_map`
  (P_z P_f θ^[r] ≫ e = e ≫ P_x θ^[r]), `derived` (F_z ≫ c = c ≫ F_x), checked against
  the three-factor definition `localFrobeniusOperator` (transport, return, θ^[n]).
  Composition order and r-1 index agree with def-weil-local-frobenius-trace. Exact.
- every cohomology group and stalk iso of a constructible sheaf: `Local.cohomology` for
  all j ∈ ℤ; `rational_heart` / `common_heart` (pullback preserves the recorded heart).
  def-weil-constructible-heart has no separate stalk notion, so the stalk iso is H^0 of
  the specified c_K; covered.
- locally closed immersion: `immersion_residue` with `[IsImmersion f₀.left]`
  (Mathlib: closed followed by open immersion): image closed, residue map iso, both
  Nat.card = q^r. Exact.
- commutation with finite coefficient extension: `composition_scalar` (canonical
  `rationalPullbackScalarComparison`, arbitrary schemes incl. semilinear maps) and
  `transport_scalar` (canonical `pointRationalFibreScalarIso`); α, e, R, c and the θ^[r]
  maps are composites of compositors, eqToIso and natural isos, so their squares follow
  formally. Maps at Ω: the Common namespace. Accepted.
- finite diagram descent: `finite_diagram_descent` over a finite quiver, functor on
  Paths, finitely many path relations; one stage L, functor A to finite-stage Weil
  complexes (inverse equations hold since objects are IsoAlgebras), isos e to the
  recorded `sfWeilStageObject`, arrow conjugacy, relations at L; no lattice
  hypothesis. I : Type u is harmless for finite I.

Edge cases: r = 1 (index 0, no identity Frobenius); f = id; empty W0 / no closed
points (Local vacuous, Pullback still meaningful); complexes outside the heart and all
j; empty quiver and zero relations; semilinear g_T is never passed to a k-linear lemma.

Dependency records: two added stmt_deps (def-zl-weil-ind-sheaf-category,
def-zl-field-weil-shriek-shift-data) are landed definition nodes, no cycle. Other used
declarations (pointRationalFibre, frobeniusPointIso, pointFdScalarExtension,
coefficientFdCohomology, sfRationalScalarExtension) belong to definition nodes reached
transitively through def-weil-local-frobenius-trace / def-weil-derived-pullback-tensor-hom;
none is owned by a theorem node. No hollow definition; every theorem is `sorry` with a
source/blueprint docstring and proof sketch; `lean.statement` is verbatim in the file.

Mismatches: none in the Lean. Only change: this section replaces the self-check (H11).
