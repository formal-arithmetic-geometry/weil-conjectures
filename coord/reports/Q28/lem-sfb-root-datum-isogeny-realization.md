## Worker report

Item: lem-sfb-root-datum-isogeny-realization. The module
`Sheaf.AlgebraicGeometry.GroupScheme.RootDatumIsogenyRealization` states
`AlgebraicGeometry.rootDatum_isogeny_realization`. Its only proof is `sorry`;
its docstring contains all eight DAG proof steps. No definition is introduced.
The item's statement, dependencies, proof and proof dependencies are unchanged.
A section 1(B) dependency interface repair is included below.

Source read: Milne, Algebraic Groups (2017), PDF pages 495--505, printed
pp.483--493: Definitions 23.1--23.2, Proposition 23.5, Theorem 23.9, Lemma 23.10,
the graph construction 23.16--23.24, and Theorem 23.25. The current blueprint
was searched under `literature/blueprint/latest/blueprint`; no existing root-isogeny
statement was found there. This supporting node is not the unit's statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
  Mathlib's `Field` is in Algebra/Field/Defs.lean:180 and `IsAlgClosed` in
  FieldTheory/IsAlgClosed/Basic.lean:62. The recorded algebraic-closure declaration
  is AlgebraicClosure in FieldTheory/IsAlgClosed/AlgebraicClosure.lean:127;
  this item requires algebraic closedness, not a chosen extension of another field.
- The characteristic exponent is `(p : ℕ) [ExpChar F p]`. ExpChar has precisely
  the characteristic-zero/exponent-one and prime-characteristic constructors
  (Algebra/CharP/Defs.lean:328--330). The exponent condition is `hq`, with
  `∃ e : ℕ, q α = p ^ e`; in particular e=0 and characteristic zero are included.
- The two group schemes and tori are `G T : Fin 2 → Grp (Over (Spec (.of F)))`.
  The index 1 is source and 0 is target. `iT` specifies their inclusions, `hG`
  reductivity, `hT` maximality, and `hsplit` the actual isomorphism with a split
  torus of some rank. Rank zero is permitted. The Grp/GrpObj interpretation is
  precisely def-sc-group-scheme's recorded interface, including the actual kernel.
- `IsCommMonObj` instances on the tori and G_m give the pointwise commutative Hom
  laws, written with `Additive`. They are structure of the already split tori,
  not an extra restriction on their isogenies.
- `aG` and `hconj` specify the actual conjugation action on each group's Lie
  algebra. `Φ`, `D`, the two Module.Finite instances, `hred`, `hroot`, `hpair`
  and `hweights` specify the actual finite reduced root datum, as in the recorded
  Borel-pair statement: roots are their actual characters, nonzero Lie weights
  are exactly Φ, and pairing a character with a cocharacter is their composition
  power map. RootDatum's perfect pairing identifies the actual cocharacter group
  with Hom_Z of the character group, so it is the node's integer dual, not an
  unrelated auxiliary lattice. No root-span or semisimplicity hypothesis occurs.
- `hcoroot` specifies that D's coroots are the geometric ones: the displayed
  reflection on characters is induced by conjugation by the actual point `n`.
  The first equation is tested on every F-algebra via `CommAlgCat.{u} F`.
  This is the normalizer-reflection characterization from Milne 21.11(d)--(e), made
  available by the dependency repair. It unpacks “root data ... as in
  lem-sfb-reductive-borel-pair-structure” rather than assuming another property
  of the proposed lattice map. Without it the old Lean interface also allowed
  abstract root data with incorrect coroots on the same character lattice.
- `u` is an additive homomorphism M₀ → M₁; `hinj` is injectivity and `hfinite`
  says that the quotient of M₁ by the actual range of u is finite.
- `b : Φ 1 ≃ Φ 0` is the root bijection; `q` is its natural-number exponent
  function. `hu` is exactly u(b(α)) = q_α α, using natural scalar multiplication.
- `hdual` is the dual relation evaluated at every character χ of T₀:
  pairing(u χ, α∨) = q_α pairing(χ, b(α)∨). Since cocharacters identify with
  the integer dual, this is precisely u∨(α∨)=q_α b(α)∨. No independent dual map
  is chosen or assumed.
- The first conjunct produces `g : G 1 ⟶ G 0` and its restriction `gT`.
  `Surjective g.hom.hom.left` is surjectivity on the underlying scheme;
  `IsFinite (GrpObj.ker g.hom.hom).hom` is finiteness of its actual identity
  fibre, hence finite-dimensional coordinate algebra over F. The equation
  `iT 1 ≫ g = gT ≫ iT 0` gives restriction, and surjectivity of gT says
  g(S₁)=S₀. Pullback of every actual character is exactly u χ.
- The second conjunct quantifies independently over EVERY `g,gT` with these
  properties. Thus the criteria concern every realization and not merely the
  particular existential witness.
- Kernel centrality is the equality `(x ≫ kerι) * y = y * (x ≫ kerι)` for
  every commutative F-algebra A and all A-points x of the scheme kernel and y
  of G₁. The first iff compares exactly this to `∀ α, q α = 1`.
- The second iff is `IsIso g ↔ (∀ α, q α = 1) ∧ Function.Bijective u`.
  For an additive homomorphism, bijectivity is equivalently an abelian-group
  isomorphism; no choice of inverse enters the statement.
- There is no reducedness, etaleness, separability, prime-to-characteristic
  index, or order restriction on the kernel. Test algebras share the base's
  universe, so their quantification is nonvacuous; affine coordinate algebras
  and the universal-point tests all occur there.

Dependency declarations used:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and `Grp`, read
  with the actual scheme interpretation in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`. This also supplies
  `GrpObj.ker`, `GrpObj.kerι` and the group structures on test-scheme points.
- `Sheaf.AlgebraicGeometry.GroupScheme.BorelPairRootDatumNormalization`:
  `AlgebraicGeometry.reductive_borel_pair_structure_with_geometric_coroots`,
  the repaired declaration of lem-sfb-reductive-borel-pair-structure. The original
  `semisimpleGroupScheme_isReductive` remains available through the public import.
- Its existing imported notions are `ReductiveTorusCentralizer.IsReductive`,
  `IsMaximalTorus`, `MultiplicativeType.splitTorus`,
  `TorusCharacterTangent.weightSpace`, `StandardGroupSchemes.multiplicative`
  and `affine`; their actual definitions and full signatures were read.
- `RankOneRoots.Character` and `Cocharacter` are the exact group-scheme Hom
  abbreviations in `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces`,
  exposed through `ReductiveRankOneReflections`; no lattice is copied.
- `RootDatum`/`RootPairing` and `RootPairing.IsReduced` are the Mathlib
  root-system definitions used by the recorded Borel-pair dependency.

All currently stated proof dependencies are imported: multiplicative-character
antiduality; reductive-rank-one-reflections; compatible-rank-one-graph-geometry;
reductive-torus-self-centralizer; reductive-root-subgroup-parametrizations;
bruhat-longest-cell-charts; and the Mathlib faithfully-flat surjective-spectrum
lemma. The Borel-pair dependency is imported publicly in its repaired form.
The remaining four proof nodes have no Lean record or Mathlib match in the
read repository: regular-cocharacter-borel-description, rank-one-frobenius-extension,
root-monomial-kernel-coordinates, faithfully-flat-group-quotient-universal.
They are only future proof inputs, not missing statement notions.

Edge cases checked mathematically before writing:

- Empty Φ: all exponent conditions and the centrality test are vacuous; tori
  are commutative, and the conclusion is exactly torus character antiduality.
- Trivial groups and rank-zero tori: permitted; no Nonempty root type is imposed.
- Characteristic zero: ExpChar forces p=1 and all q=1, as required by Milne.
- Frobenius of SL₂ in characteristic p: q=p and u=p on characters. Its root
  kernel is infinitesimal and noncentral; the first criterion says precisely that.
- SL₂ → PGL₂ in characteristic two: q=1, cokernel has order two, kernel μ₂
  is nonreduced and central. The statement includes it and does not call it
  an isomorphism.
- The exceptional characteristic-two B/C isogenies have a torus isomorphism
  with some q>1. Bijectivity of u alone is deliberately insufficient, as in
  Milne's warning following Proposition 23.5.
- A degree-p power map on G_m has empty roots and central nonreduced μ_p kernel;
  it fails the isomorphism test because u is not bijective.
- The fake GL₂-coroot example below detects the inherited interface fault.

Searches actually run, with logged service results:

- msearch leanfinder: “An injective character lattice map with finite cokernel
  and characteristic-power root and coroot scalings is induced by an isogeny
  of split reductive groups”. Eight hits, headed by RootPairing.coroot and
  RootPairing.polarizationIn_Injective; no group-scheme realization statement.
- msearch loogle: `RootPairing.Hom`. Twelve hits; read Hom.lean:58--78.
  These maps preserve roots and coroots with exponent one and give no group
  realization, so they do not state the item.
- msearch grep: `isogen|Isogen|reductive` in Mathlib/AlgebraicGeometry.
  Zero hits.
- msearch leansearch: “An isogeny of root data is realized by an isogeny of
  split reductive group schemes”. Eight hits, including RootDatum and abstract
  RootPairing equivalences, with no realization theorem.
- rg `isogen|Isogen|root_datum|RootDatum` in the project's GroupScheme sources;
  rg `root_datum_isogeny_realization|rootDatum_isogeny|isogeny.*root|root.*isogeny`
  in lean/Sheaf and lean/WeilConjectures; rg of the item id in WeilConjectures.
  No exact declaration exists. CentralLatticeEnlargement and
  ChevalleyIntegralRootModel cite this item only in proof docstrings.
- Read RootSystem/Defs.lean:81--109 and Hom.lean:58--78 to distinguish actual
  abstract root-data objects and maps from group-scheme isogeny realization.

Validation: scompile.py compiled both modules separately in dependency order
against the live library, including the dependency as a private overlay. The
recorded times were 2.2 s and 2.5 s. No errors or non-sorry warnings.
Both files set autoImplicit false and have no lines over 100 characters.

## Dependency modules

`lem-sfb-reductive-borel-pair-structure` receives a lean-only section 1(B) repair
in `Sheaf.AlgebraicGeometry.GroupScheme.BorelPairRootDatumNormalization`.
Its statement, source, statement dependencies, proof, and proof dependencies are
unchanged. The old signature is retained clause by clause, followed by the actual
normalizer-conjugation characterization of every coroot. The existing semisimple
clause is reused by public import, rather than redeclared.

Why the former record is insufficient: take the standard GL₂ root lattice
X=Z², roots ±(1,-1), cocharacter lattice Z², and the usual dot-product pairing.
Replacing the positive coroot (1,-1) by (1+c,-1+c), with its negative for the
negative root and c any nonzero integer, still satisfies the old abstract
RootDatum axioms, reducedness, root normalization, composition pairing, and
actual Lie-weight condition. The reflection sends the two roots to their
negatives and has order two, but is not the action of a GL₂ normalizer element:
the only nonidentity Weyl action is the coordinate swap. Thus those hypotheses
alone do not specify GL₂'s coroots. In particular the old record cannot provide
the actual root datum required by the realization theorem. The repaired
conclusion is precisely the geometric coroot datum already described by the
node's source and its proof step 6 (normalizer reflections from Theorem 21.11).
It does not change the mathematical node or any unit statement.

The repaired signature preserves: existence of the split Borel pair; the
universal quantification over every such pair; proper finite-type flag quotient;
flat surjective right B-torsor and its kernel-pair square; the largest unipotent
radical; the projection splitting off the torus with kernel U; multiplication
U×T≅B; finitely generated actual character/cocharacter groups; reduced root datum;
actual conjugation actions; roots and the composition pairing; exact Lie(G)
weight condition; and exact positive Lie(B) weight condition. The additional
last clause says the root reflection is induced by conjugation by n on every
algebra and has the displayed character formula. Its natural-language proof
is the existing nine-step proof, with the normalizer output of step 6 retained.

## Second reading by Q28

Author's final reread, with both node JSONs, both modules, and Milne open.
No independent agent was started, following the dispatcher instruction; the
maintainer supplies the independent delivery review. I checked that the
existential map and the universal criteria are separate conjuncts; that u runs
contravariantly; that b maps source roots to target roots; that hdual has the
correct scalar and direction; and that centrality tests the scheme kernel on
all algebra points. I found the coroot-normalization gap during this reread
and repaired the dependency record rather than silently assuming a new
property of u. The main theorem consumes exactly that repaired geometric
coroot specification. The dependency's original clauses and semisimple theorem
are preserved. No new node and no item statement correction were needed.
