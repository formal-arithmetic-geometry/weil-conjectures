## Worker report

The module `Sheaf.RingTheory.CompleteLocalSmoothPowerSeries` states the entire node in two
named theorems, each with proof `sorry`. The main theorem is
`AlgebraicGeometry.ArtinDeformation.formallySmoothOnArtin_iff_powerSeries`; the last clause
is `AlgebraicGeometry.ArtinDeformation.prorepresented_unobstructed_powerSeries`.
The five preceding helpers have real data and define only the canonical constructions
appearing in this node. No independent extra notion or duplicate category is introduced.

Source read: `literature/stacks-project/formal-defos.tex`, Tag 06HL,
`lemma-smooth-morphism-power-series`, statement and complete proof (lines 2024 onward);
Tag 06ST, `example-tangent-space-map-prorepresentable-functor` (lines 3388 onward).
The eight inherited proof steps are retained in the two theorem docstrings, with their
DAG dependencies. No statement correction and no disputed mathematical statement.

Hypothesis and clause matching:

* The field is `{k : Type u} [Field k]`. The common universe u contains k and all
  ring carriers and Artinian tests; it is arbitrary, and test rings are in the same
  universe as A and B, never in an independent smaller universe. The value universe
  v of the arbitrary functor in the corollary is independent.
* `B A : CompleteLocalAlgebra k k` supplies commutative k-algebras `B.ring`, `A.ring`,
  local-ring instances, `IsNoetherianRing`, maximal-ideal `IsAdicComplete`, and the
  specified k-algebra residue-field equivalences. These are precisely the common
  residue-field complete Noetherian local algebras in the node.
* `f : B.ring →ₐ[k] A.ring`, `[IsLocalHom f.toRingHom]`, and `hf` give the k-algebra
  map, locality, and continuity with both maximal-ideal-adic topologies written out.
  `hres : (completeAugmentation A).comp f = completeAugmentation B` says that the
  marked residue maps agree, hence that the induced residue map is the identity.
  `completeAugmentation` is exactly the specified residue equivalence after the
  canonical quotient map, not an arbitrarily chosen augmentation.
* The test category is the existing `TestCategory k k`: its objects have
  `IsArtinianRing`, locality, and an augmentation onto k with maximal kernel;
  this is the given residue marking. `IsArtinianRing` is the descending chain
  condition on ideals. Its arrows preserve that marking and are automatically local.
* `LocalMap A R` is exactly h_A(R), and likewise for B. It retains the k-algebra
  map, locality and marked residue equation. Every local map sends m_A^n into
  m_R^n for all n, so it is continuous in the specified adic topologies. Thus the
  existing LocalMap encoding drops no continuity condition and adds none.
* `IsFormallySmoothOnArtin B A f` quantifies over all `p : R' ⟶ R` with
  `Function.Surjective (map p)` and `(RingHom.ker (map p).toRingHom)^2 = ⊥`.
  The compatibility equation on `a : LocalMap A R` and `b : LocalMap B R'` is the
  fibre-product condition. The existential a' with both composition equations is
  precisely surjectivity onto that fibre product. The test includes zero kernels;
  it is not restricted to principal or small extensions.
* `relativeCotangentRelations B A f` is the pullback to m_A of
  `Ideal.map f m_B ⊔ m_A^2`, with scalars restricted to k. Locality puts this ideal
  inside m_A, so its pullback is exactly the intended denominator, not a different
  intersection. `RelativeCotangent B A f` is its literal quotient of m_A.
* The right side of the iff uses
  `MvPowerSeries (Fin (Module.finrank k (RelativeCotangent B A f))) B.ring`.
  The k-algebra equivalence e has `∀ b, e (f b) = MvPowerSeries.C b`; this is exactly
  B-linearity for the given structural map, without choosing another B-algebra
  structure on A. Continuity of e and its inverse is explicitly included, giving
  the complete local B-algebra isomorphism. Every ring equivalence of local rings
  is local, so a separate arbitrary locality certificate is unnecessary.
* `RelativeTangentPoints B A f` is the actual fibre of dual-number A-points over
  the constant B-point, using the shared `squareZeroTest k` (k plus k with square-zero
  second summand). Its augmentation and k-algebra structure are those of the shared
  construction. The constant point is the canonical k-algebra structural map after
  `completeAugmentation B`.
* The second conjunct identifies that fibre with
  `Module.Dual k (RelativeCotangent B A f)`. It specifies the equivalence on every
  representative x by `e a (mkQ x) = (a.val.hom x).snd`. This specifies the canonical
  identification, not just an unrelated bijection. Addition and scalar multiplication
  of tangent points are addition and scalar multiplication of the second coordinate;
  evaluation on every quotient representative proves that the identification
  preserves exactly those operations. No prechosen arbitrary vector-space structure
  on the point set is an extra hypothesis.
* For the final clause, `F : TestCategory k k ⥤ Type v` is any set-valued functor.
  `eF R : LocalMap A R ≃ F.obj R` and `hnat` give its prorepresentation by A.
  Naturality is expanded on pairs with the actual postcomposition equation; such
  pairs are exactly the action of h_A on arrows, so this is precisely a natural
  isomorphism, without defining a second h_A functor with redundant data.
  `hunobstructed` says `F.map p` is onto across every square-zero surjection.
  The conclusion gives the continuous k-algebra power-series isomorphism with
  `Module.finrank k m_A.Cotangent` variables. Its second conjunct identifies
  `F.obj (squareZeroTest k)` with `Module.Dual k m_A.Cotangent`, and specifies the
  same second-coordinate formula after eF. Hence this integer is the tangent-space
  dimension, since m_A/m_A^2 is finite dimensional. This includes arbitrary
  prorepresenting natural identifications, not only F = h_A.

Dependency declarations read and used:

* `def-weil-field`: Mathlib `Field`, Algebra/Field/Defs.lean:180, full class and docstring.
* `def-weil-pbc-noetherian-ring`: Mathlib.RingTheory.Noetherian.Defs,
  `IsNoetherianRing` and `isNoetherianRing_iff_ideal_fg` (around lines 196--207).
* `def-weil-pbc-adic-completion`: Mathlib.RingTheory.AdicCompletion.Basic,
  `IsAdicComplete` (Hausdorff plus precomplete, line 56) and `AdicCompletion`
  (compatible sequences of quotient classes, line 171). The bundled complete local
  algebra uses exactly this completeness, not a new topological substitute.
* `def-weil-pbc-multivariate-power-series`: Mathlib.RingTheory.MvPowerSeries.Basic,
  `MvPowerSeries` (line 86), finite family indexed by Fin r, usual coefficient algebra.
* Added already-landed `def-sfb-artin-deformation-test-category`, module
  Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory: `TestCategory`, `IsTestAlgebra`,
  `CompleteLocalAlgebra`, `LocalMap`, `ring`, `map`, `squareZeroTest`, `squareZeroAlgebra`.
  I read the whole module, including the actual square-zero multiplication and its
  canonical scalar restriction. This node supplies the notions stated inline in the
  item; its R = k specialization imposes no extra condition, because k is Noetherian
  and finite type over itself. This dependency has no route back to the item (checked
  by traversing stmt_deps and proof_deps). No dependency module needed repair.

Proof-only imports are precisely the available recorded proof-dependency modules:
PowerSeriesQuotientVariables, PowerSeriesCompleteOverCompleteBase,
PowerSeriesAdicEvaluation, PowerSeriesCombinedIdealCoefficients (all upstream
WeilConjectures.RingTheory), and Sheaf.RingTheory.CompleteLocalCotangentSurjectivity.
I read their signatures and docstrings. The remaining proof dependencies are Mathlib
leaves in MvPowerSeries.Equiv/Inverse, HopkinsLevitzki (already publicly imported by
the Artinian framework), and Ideal.KrullsHeightTheorem. The cotangent-surjectivity
node is used only as a proof import, not as a substituted definition of our quotient.

Searches actually run:

* msearch leanfinder: "Formally smooth maps of complete noetherian local k algebras
  with residue field k are power series extensions". Eight hits, principally
  Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete and ordinary formal
  smoothness; no exact complete-local Artinian test/power-series iff.
* msearch loogle: "MvPowerSeries, Algebra.FormallySmooth". Zero hits.
* msearch grep: "FormallySmoothAdic|relativeCotangent|Prorepresent", RingTheory.
  Zero hits from that service; not used to infer that the upstream adic notion is
  absent. Direct source search found and read WeilConjectures.RingTheory.FormallySmoothAdic.
* msearch leansearch: "A formally smooth morphism of complete noetherian local
  algebras with residue field k is a power series extension". Eight ordinary formal
  smoothness hits, no exact theorem. Ordinary FormallySmooth and the upstream adic
  test quantify over arbitrary target algebras, not this definition of the Artinian
  functor lifting test; neither was silently substituted for the node's test.
* Direct rg of lean/WeilConjectures and lean/Sheaf for relativeCotangent,
  relativeTangent, FormallySmoothAdic, Prorepresent, dual numbers and Artinian
  categories found the shared ArtinDeformationTestCategory, which is reused.
  Searching the item id in WeilConjectures found no existing declaration.
* Direct rg of Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json for
  every new declaration name found none. Searches for smooth/power-series theorems
  found the augmentation-completion and Cohen/adic parameter theorems; their
  hypotheses and conclusions differ from this Artinian representable-functor theorem.
* I also read WeilConjectures.Mathlib.RingTheory.Ideal.Cotangent, with the existing
  AlgHom.toDualNumber and cotangentForm, to check the canonical tangent formulas.
  They describe absolute cotangents at an augmentation; the relative fibre and
  presentation criterion here are absent. No copy of these maps is defined.

Edge cases checked before the statement was finalized:

* r = 0 and A = B: the denominator is m_A, the quotient and relative tangent
  dimension are zero, and power series with Fin 0 variables is B. The zero-variable
  ring is never replaced by an expression requiring a nonempty variable family.
* B = k: m_B = 0, so the relative cotangent is m_A/m_A^2. The second theorem
  explicitly specializes to this case with the correct tangent dimension.
* A = k gives dimension zero and the singleton point functor, so unobstructedness
  and the zero-variable presentation agree.
* The obstructed ring k[t]/(t^2) fails the lifting test for
  k[t]/(t^3) → k[t]/(t^2): the image t cannot square to zero after lifting.
  This agrees with the failure of a power-series presentation in every characteristic.
* Identity test maps and maps with kernel zero are allowed by the square-zero test.
  Arbitrary fields, including positive characteristic, are allowed.
* The zero ring is correctly excluded by the specified nonzero residue field k.
  All k-algebra residue markings are retained.

Validation: scompile.py checked the delivered module both as sandbox and under its
actual module name, cleanly (2.9 s and 2.8 s). The first compile exposed a missing
Ideal.Cotangent import and a difference between the shared square-zero algebra's
scalar structure and the default dual-number scalar structure. The final file imports
Ideal.Cotangent and uses Algebra.ofId into the actual shared ring; no typeclass
assumption or universe equality was added to hide the difference.

## Second reading by Q12

The dispatcher explicitly prohibits starting other agents; this section records the
worker's separate consistency pass, not an invented independent reviewer. The
maintainer's independent delivery review remains required.

I reread the node beside the final file. Both noetherian-completeness hypotheses are
inside CompleteLocalAlgebra; continuity and residue identity of f are explicit. The
lifting property uses all Artinian square-zero surjections and includes both equations
of the lift. The quotient is literally the restriction of m_B A + m_A^2 to m_A.
The equivalence preserves the given B-map and is continuous in both directions.
The tangent statement is for the constant B-fibre, with the canonical second-coordinate
formula for every maximal-ideal representative. The final theorem retains any F with
natural prorepresenting equivalences and transports its square-zero surjectivity;
its tangent identification shows why the number of variables is its tangent dimension.

The consistency pass checked that `map` has the direction R' → R, so the two
compatibility equations have the correct orientation, and that `hnat` uses the
same direction. It checked the Fin 0 and obstructed dual-number cases above. No
mathematical mismatch was found. The compiler fixes reported above concern only
the exact shared square-zero interface and the missing Mathlib import. The final
source has no auto-bound variables, local notation, private declarations or proofs
beyond the two expected `sorry` theorem bodies.
