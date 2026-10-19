## Worker report

Repair of returned immutable head 50eefef7fcb5. The supplied sandbox had only dispatcher
brief markers, so the item JSON was copied afresh from current shared main, retaining
its reviewed five-step proof and split_report verbatim. In particular the unauthorized
split_report.summary edit of the returned head is absent. The new file is
lean/Sheaf/AlgebraicGeometry/EtaleGenericDirectImageExchange.lean.

The sole postponed theorem is AlgebraicGeometry.Etale.genericDirectImageExchange.
Three real helper definitions in its owning module package the canonical squares and
the two-clause conclusion; none introduces any arbitrary exchange map or chosen
isomorphism. No new DAG node or statement correction is needed.

Hypothesis-by-hypothesis translation:

- Algebraically closed base field F: `(F : Type u) [Field F] [IsAlgClosed F]`.
- Integer N at least one, invertible in F: `(N : ℕ) (hN : 1 ≤ N)` and
  `(hNF : IsUnit (N : F))`. Natural numbers with the positive bound give exactly
  the positive integers of the node.
- Finite commutative ring A with NA=0: `(A : Type (u + 1)) [CommRing A]
  [Finite A] (hNA : ∀ a : A, N • a = 0)`. The zero ring remains allowed.
- B is an F-scheme: `(B : Scheme.{u}) [B.Over (Spec (.of F))]`.
- Smooth and integral: `[Smooth (B ↘ Spec (.of F))] [IsIntegral B]`.
- Finite type: `[LocallyOfFiniteType (B ↘ Spec (.of F))]
  [QuasiCompact (B ↘ Spec (.of F))]`.
- Dimension one: `(hBdim : topologicalKrullDim B = 1)`; this is absolute
  topological Krull dimension, not a relative-dimension replacement.
- A nonempty affine open: `(U : B.Opens) (hU : IsAffineOpen U) [Nonempty U]`.
- Its coordinate fraction field Q: `(Q : Type u) [Field Q]
  [Algebra (B.presheaf.obj (op U)) Q]
  [IsFractionRing (B.presheaf.obj (op U)) Q]`. The coordinate ring is Γ(B,U).
  The generic map is explicitly `Spec.map (CommRingCat.ofHom (algebraMap
  (B.presheaf.obj (op U)) Q)) ≫ hU.fromSpec`, rather than an unconstrained map.
  Thus arbitrary presentations of the fraction field, including B.functionField
  through functionField_isFractionRing_of_isAffineOpen, are covered.
- Algebraically closed algebraic extension L/Q: `(L : Type u) [Field L]
  [Algebra Q L] [IsAlgClosed L] [Algebra.IsAlgebraic Q L]`. The map Spec L → Spec Q
  is `Spec.map (CommRingCat.ofHom (algebraMap Q L))`. No separability is imposed.
- Finite-type B-schemes: `(T Y : Over B)` with LocallyOfFiniteType and
  QuasiCompact instances on both T.hom and Y.hom.
- A B-morphism h which is qcqs: `(h : T ⟶ Y) [QuasiCompact h.left]
  [QuasiSeparated h.left]`. Over enforces compatibility with the structure maps.
- Bounded-below E with constant A coefficients: `(E : DerivedCategory.Plus
  (Sheaf T.left.smallEtaleTopology (ModuleCat.{u + 1} A)))`; E.obj is its image
  in the ordinary unbounded `Etale.DerivedCategoryModule A T.left`. This uses
  the recorded encoding of constant-ring modules, without changing sites.

Clause-by-clause translation (unfold genericDirectImageExchangeConclusion):

- W_Q is `pullback W.hom q`, and W_L is `pullback W.hom (l ≫ q)`, where q is
  the explicit ordinary generic projection above and l is the field-extension map.
  These are exactly the scheme-base-change corners of def-pc-base-change;
  `moduleBaseChange` is that record's module-sheaf clause, not its scheme carrier.
  The morphisms h_Q and h_L are the `.left` maps of `(Over.pullback q).map h`
  and `(Over.pullback (l ≫ q)).map h`.
- genericDirectImageFirstSquare has first projections as horizontal arrows.
  genericDirectImageSecondSquare has the existing `baseChangeMap` arrows
  k_W:W_L → W_Q. Its commutativity follows from the pullback projections.
  The outer rectangle's horizontal map is k_W ≫ pr_Q = pr_L, by the defining
  pullback.map first-projection equation; l ≫ q is the Spec map of the composite
  coordinate-ring map. Hence this rectangle is precisely the node's square,
  with chosen W_L corners, even though the projection is written as a composite.
- The first conjunct is `IsIso` of `.app E.obj` of the recorded
  `Etale.exactDerivedBaseChangeMap (ModuleCat A)` for this outer rectangle.
  This is the specified unbounded adjunction mate, not a bare endpoint isomorphism.
- The second conjunct equates that SAME morphism with the four-arrow composite:
  `(moduleInverseImageCompIso A g_YQ k_Y).inv` at Rh_*E;
  inverse image by k_Y of the ordinary-generic exchange;
  the second-square exchange at g_TQ^*E;
  Rh_L* applied to `(moduleInverseImageCompIso A g_TQ k_T).hom` at E.
  These are exactly the comparisons of the recorded
  moduleExchange_composite_baseChange theorem. In particular the second exchange
  uses W_L, not an unidentified iterated fibre product. The proof docstring explains
  its canonical comparison to the field-extension theorem's iterated corners.

Dependency declarations read and used:

- WeilConjectures.AlgebraicGeometry.DerivedCategories and
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients:
  AlgebraicGeometry.Etale.DerivedCategoryModule, Mathlib DerivedCategory.Plus
  and its obj inclusion, the underlying sheaf/coefficient encoding.
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact:
  AlgebraicGeometry.etaleInverseImageModulesExact supplies the constant-module
  interpretation and exactness. The statement uses the exact ModuleCat upperStar
  functor specified by ExactUnboundedExchange, rather than an existential witness.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth.
- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsIntegral.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact:
  AlgebraicGeometry.LocallyOfFiniteType and AlgebraicGeometry.QuasiCompact.
- Mathlib.Topology.KrullDimension: topologicalKrullDim.
- WeilConjectures.AlgebraicGeometry.BaseChangeConventions:
  Scheme.Modules.moduleBaseChange and its explicit documentation of pullback,
  Over.pullback, baseChangeMap, first/second projections and iterated comparison.
- Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated:
  AlgebraicGeometry.QuasiSeparated, exactly quasi-compact diagonal.
- WeilConjectures.SixFunctors.BaseChange.Derived:
  Etale.derivedBaseChangeMapPlus (the bounded-below mate used in the proof plan),
  available through the stated field-extension comparison dependency.
- Sheaf.AlgebraicGeometry.ExactUnboundedExchange:
  Etale.exactDerivedBaseChangeMap and exactDerivedSquareUpperStarIso.
- Sheaf.AlgebraicGeometry.ModuleExchangeCompositeBaseChange:
  Etale.moduleInverseImageCompIso and moduleExchange_composite_baseChange.
- Mathlib.AlgebraicGeometry.FunctionField:
  functionField_isFractionRing_of_isAffineOpen and IsAffineOpen.fromSpec.

The recorded proof dependencies are imported without public when only the proof
needs them. Their signatures/docstrings were read, including the Stacks smooth-limit
and field-extension statements, unbounded/Plus comparison, coefficient-forgetting
conservativity and pasting formula. Missing local upstream files were read with
scompile.py --source (BaseChangeConventions, DerivedCategories,
EtaleInverseImageModulesExact, SpecStalkLimitAffineNeighbourhoods). No source tree
or live module was modified.

Edge cases checked before writing and again in the second pass: E=0; empty T or Y;
h=identity; open immersions; A the zero ring; N=1 (forces the zero ring); arbitrary
positive characteristic with N prime to it; purely inseparable parts of L/Q;
nonseparated integral smooth B such as the doubled-origin curve. No separatedness,
properness, constructibility, finite Tor amplitude or characteristic-zero hypothesis
has been added. Nonempty U excludes exactly the invalid empty coordinate-ring
fraction-field construction. All scheme, field and site universes are explicit;
the coefficient universe is the recorded u+1 convention.

Searches (2026-10-17 UTC):

- msearch.py leanfinder, query "Canonical derived etale direct image commutes with
  geometric generic fibre for finite constant ring coefficients": eight hits,
  including StandardEtalePair.HasMap.map, RingHom.Etale.isStableUnderBaseChange,
  Algebra.Etale.comp and Algebra.IsEtaleAt.comp. No derived-exchange match.
- msearch.py loogle, query `"baseChange"`: twelve hits on Lean logging and
  Submodule/LinearMap/LinearEquiv scalar extension; no derived-etale statement.
- msearch.py grep, query `(generic.*[Ee]xchange|[Ee]xchange.*generic)`: no Mathlib hits.
- rg of that pattern and the item id in the upstream WeilConjectures and shared
  lean/Sheaf: related EtaleGenericExchangeAlgClosed and OpenDirectImageOverField,
  but no statement of this direct-image lemma. The former is the downstream closed
  support/internal-Hom result and is deliberately not imported, avoiding a cycle.
- rg for base-change squares and baseChangeMap found no public existing wrapper for
  these two chosen-corner CommSq packages. Existing canonical maps are reused.

No disputed mathematical statement was found. The reviewed mathematics is unchanged.

## Dependency modules

`def-weil-quasi-separated-morphism`: its mathlib_match already points to the exact
Mathlib class. As specifically requested in the return, the dependency copy gains an
existing:true lean record for Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated /
AlgebraicGeometry.QuasiSeparated, with lean.note explaining the attachment repair.
No new module or duplicate definition is introduced; all other fields are unchanged.

## Second reading by Q53

A separate fresh reading of the node, source statements and completed Lean text was
performed by the same dispatcher worker; no second agent was started. The maintainer's
independent delivery review remains the independent reading.

The pass matched F, N's positivity and invertibility, finite commutative A and its
annihilation, B's smoothness/integrality/finite type/absolute dimension, nonempty affine
U, the coordinate fraction field, algebraic algebraically closed L/Q, finite-type
T/Y over B, qcqs h and E in D+ to the exact binders listed above. It unfolded the
conclusion definition and checked both the IsIso conjunct and equality of actual
canonical morphisms, including the source and target composition identifications.
It checked the second square's chosen W_L corners and the equality of its pasted
horizontal projections with the direct first projections, rather than confusing
W_L with (W_Q)_L. It found no mathematical mismatch and no change to the node needed.
The five proof steps and sources are in the theorem docstring, not just in this report.
The dependency repair is an existing exact Mathlib attachment. The split_report is
identical to main; the only item/dependency field changed is lean. This repairs H1,
H2, H3, H8 and H11 in the return; H10 is checked by the required per-file compilation
and the final dry run below.

Compilation repair notes: the first pass found that unqualified baseChangeMap resolved
to Etale.baseChangeMap (the coefficient-level exchange), so all scheme maps now use
AlgebraicGeometry.baseChangeMap explicitly. The two CommSq-valued definitions
retain their fully constructed commutativity proofs, with a declaration-local
linter.defProp exemption because these are named canonical-square packages, not
postponed mathematical assertions. The second pass typechecked the sandbox and
final module and found only two long lines; both were wrapped before the final
clean compile and dry run. No hypothesis or conclusion changed.

Final scompile.py result: exit 0, no Lean warnings or errors, for both the sandbox
check and the final Sheaf.AlgebraicGeometry.EtaleGenericDirectImageExchange module.
Each compiler invocation retains the prescribed 60-second limit; wrapper timings
include slot/transport overhead. The sole theorem remains sorry as required by stage 2.
