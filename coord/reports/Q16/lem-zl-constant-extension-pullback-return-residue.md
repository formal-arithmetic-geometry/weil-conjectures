## Worker report

The module `Sheaf.Paper.ConstantExtensionPullbackReturnResidue` states the node in two
parts: `WeilConjectures.constantExtensionPullbackReturn` gives restriction, exactness,
and cyclic normalization before direct image;
`WeilConjectures.constantExtensionResidueCompositum` gives the compatible residue
quotient, generation, degrees and cardinality. Neither theorem is proved. The two
additional postponed helper theorems belong to the same node and have proof docstrings.
All five definitions have actual data. The repair adds a definition-ownership node
for three existing sheet declarations and the three missing statement dependencies;
no Lean implementation or mathematical statement changes.

Hypotheses and clauses, checked against the original node:

- The datum `(p,a,q,k₀,k)` is the existing `D : FiniteFieldDatum.{u}`; its prime,
  positive exponent, cardinality, fixed closure and algebra structure are its fields.
  The independent coefficient universe is `v`, with `Ω : Type v`, `[Field Ω]`,
  `[Algebra (Padic l) Ω]`, `[IsAlgClosure (Padic l) Ω]`, `[Fact l.Prime]` and
  `hl : l ≠ D.p`. No complex embedding or lissity hypothesis is imposed.
- The separated finite-type model is `X₀ : Over (Spec (.of D.k₀))` with
  `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]`.
  These are exactly finite type and separatedness. The geometric fibre is the existing
  `D.geometricFiber X₀`, not a replacement scheme.
- `m : ℕ` and `hm : 1 ≤ m` include every positive extension degree.
  `D.extensionSubfield m hm`, `constantExtensionDatum D m hm`,
  `constantExtensionModel D m hm X₀`, and `constantExtensionOriginalModel D m hm X₀`
  give exactly the specified `k_m`, its finite-field datum, the `k_m` model and its
  original-base interpretation. The projection is `constantExtensionProjection`;
  its geometric base change is the `zlFiberMap` used by `zlWeilPull`.
- The coefficient and Weil categories are literally `sfCommonStageWeilSheaf` on the
  `sfCommonStageHeartProperty` in `generalAlgebraicallyClosedConstructibleCategory`.
  Geometric Frobenius is `D.geometricFrobenius`. The restriction specification and
  its iterate use actual common-stage pullback; all composition arrows are `zlPullComp`,
  descended from the specified integral composition arrow and finite reductions.
- The functor `R` in `constantExtensionPullbackReturn` goes from the original Weil
  heart to the `k_m` Weil heart. `ConstantExtensionRestrictionSpec ... R` supplies
  a natural carrier comparison through the actual `constantExtensionFiberIso`
  and the equation identifying the structure map with
  `constantExtensionWeilIterate ... (m - 1)`, namely theta^[m]. This definition was
  opened and read: its comparison is a natural isomorphism of carrier functors,
  so on every morphism the new carrier map is the old map under that identification.
  Its structure equation includes `constantExtensionRestrictionComparison`, with the
  specified compositor, fibre-return identity and actual iterated arrow.
- `PreservesFiniteLimits R ∧ PreservesFiniteColimits R` expresses exactness on these
  abelian hearts (including additivity). There is no extra equivalence assumption
  on `R` and no assumption on its input sheaf.
- `ConstantExtensionPullbackNormalization ... R G` describes the actual gluing by
  natural coordinate isomorphisms `γ i` from the carriers of `G` on the semilinear
  sheets to the carrier of `R`. It uses the existing `constantExtensionSheetPullAt`.
  `constantExtensionCoordinateStep` is exactly pullback of the Weil arrow after
  the normalized composition comparison. Its equation with `γ i` and `γ j`
  specifies identity transitions for every adjacent pair `j=i+1`.
- The second normalization equation identifies the full return of `G` on sheet zero
  with the Weil structure of `R`. After the intermediate transitions are identities,
  this specifies its last transition to be theta^[m], with no arrow omitted.
  `constantExtensionZerothCoordinateIso` only removes composition with the identity
  at index zero; it is `eqToIso` of the category identity law. The coordinate
  successor theorem expresses the powers of the actual `H`, not k-linearity.
- `Nonempty (G ≅ zlWeilPull ... (constantExtensionProjection ...))` is the natural
  isomorphism of Weil functors from this gluing to the actual original-base pullback.
  The normalization compares all arrows, not just bare carriers or stalks.
  This entire statement precedes any direct image and uses none.
- In `constantExtensionResidueCompositum`, `z` is an arbitrary point together with
  membership in `closedPoints` of the actual extension model. Its first conclusion
  is closedness of the actual image under `constantExtensionProjection`.
- The residue tensor is the existing commutative-ring pushout of the two actual
  base maps `X₀.hom.residueFieldAlgebraMap x` and `D.extensionEmbedding m hm`.
  This is kappa(x) tensor_{k₀} k_m, with its literal factor inclusions. The tensor
  map is `pushout.desc` of the actual residue-field map of `g_m` and the actual
  `k_m`-structure map. `constantExtensionResidue_compatible` is the base-square
  compatibility needed by this constructor, not an added hypothesis.
- The selected prime is `RingHom.ker (constantExtensionResidueTensorMap ...).hom`.
  The theorem asserts `IsField` of its quotient and a `RingEquiv` from that quotient
  to the actual residue field with composite along `Ideal.Quotient.mk` equal to
  the actual tensor map. Composing this equation with the two pushout inclusions
  gives compatibility with both specified residue maps; no arbitrary embedding or
  split component has been selected instead. The kernel is prime because the
  target is a field.
- Generation by the two images is stated explicitly as
  `Subfield.closure (Set.range ... ∪ Set.range ...) = ⊤` in kappa(z).
- `localClosedPointDegree D X₀ (constantExtensionClosedImage ... z)` is `d`,
  using precisely the original structure map to put the `k₀`-algebra structure on
  its residue field. `localClosedPointDegree D (constantExtensionOriginalModel ...) z`
  is `R`, the degree of the new residue field over the original finite field,
  not its degree over `k_m`.
- `constantExtensionResidueDegree ... z.val` is `f`, defined using the actual
  residue-field homomorphism of the projection. The final four conclusions are,
  in order, `R = Nat.lcm d m`, `f = R / d`, `f = m / Nat.gcd d m`, and
  `Nat.card kappa(z) = Nat.card kappa(x) ^ f`. No degree symbol is an arbitrary
  natural number disconnected from the actual residue extension.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `.extensionSubfield`, `.extensionEmbedding`, `.geometricFiber`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `WeilConjectures.FiniteFieldDatum.geometricFrobenius`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`, the actual
  `GeneralAlgebraicallyClosedCoefficients.Pair` common-stage category.
- `Sheaf.Paper.SfConstructibleHeart`: `WeilConjectures.sfCommonStageHeartProperty`;
  its full heart `sfCommonStageHeart` and abelianity statement were read.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilComplex`,
  `sfCommonStageWeilSheaf`, `sfCommonStageWeilForget`,
  `sfCommonStageWeilFrobeniusPullback`, `sfWeilPrimeInvertible`, all in
  `WeilConjectures`.
- `Sheaf.Paper.WeilIndSheafCategory`: `WeilConjectures.zlWeilPull`, `zlFiberMap`,
  `zlPullComp`, `zlIntegralPullComp`, `zlFrobeniusSquare`; the heart and ambient
  ind interfaces remain the dependency's existing constructions.
- `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence`: the recorded declarations
  `constantExtensionDatum`, `constantExtensionModel`, `constantExtensionOriginalModel`,
  `constantExtensionProjection`, `constantExtensionSheet`, `constantExtensionFiberIso`,
  `constantExtensionHeartForget`; also its existing same-notion helpers (owned by the definition nodes listed below)
  `constantExtensionWeilIterate`, `constantExtensionReturnComparison`,
  `constantExtensionRestrictionComparison`, `ConstantExtensionRestrictionSpec`,
  `constantExtensionSheetPullAt`, `constantExtensionSheetPull`,
  `constantExtensionClosedImage`, `constantExtensionResidueDegree`. The theorem
  `constantExtensionWeilHeartEquivalence` is not invoked as a hypothesis or used
  to choose any data. Its stronger conclusion (and complex embedding binder) is
  not substituted for this node's statement.

Proof dependency imports are plain rather than public:
`Sheaf.CategoryTheory.CyclicReturnExactEquivalence` (the full signature and
`cyclicReturnIso`, `cyclicConstantObj` read),
`Sheaf.AlgebraicGeometry.ClosedPointField` (closed iff finite residue extension),
`WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField`
(`Scheme.Pullback.exists_residueField_equiv_ofPointTensor`, including both
compatibilities), `Mathlib.FieldTheory.Finite.Basic` (the Frobenius automorphism,
its order, and its bijective powers), and `Mathlib.LinearAlgebra.Dimension.Free`
(`Module.finrank_mul_finrank`). `integralPullbackComposition` is already available
through the public owning interface and is the normalization used by `zlPullComp`.
The proof dependency `lem-zl-constant-extension-sheet-heart-coordinates` has no
recorded Lean declaration at this reading, so there is no module to import for it;
it is proof-only, and none of its results was replaced by an extra hypothesis.
The parent theorem module owns the already recorded canonical definitions; adding
an import from that module back to this one would close an import cycle and must
be omitted by the maintainer.

Edge cases checked before and after writing:
`m=1` has only index zero and no `j=i+1` pair, so the normalization asserts exactly
one return arrow; theta^[1] is the existing iterate at index zero. An empty model
is permitted and all closed-point assertions are vacuous. Disconnected schemes,
zero sheaves, nonlisse sheaves and Jordan blocks have no additional restrictions.
For `(d,m)=(1,m),(2,3),(2,4),(m,m)`, the formulas give respectively
`f=m,3,2,1`; in the noncoprime case `(2,4)` the selected nonsplit tensor quotient
has degree 4 over the base, with no demand that the tensor itself be a field.
Universes `u` and `v` remain independent. No field, scheme or sheaf nonemptiness,
connectedness, smoothness, rational point or semisimplicity is imposed.

Searches made before writing (2026-10-24 UTC):

- `msearch.py leanfinder`, query “Restriction of a Weil sheaf to a finite constant
  field extension is Frobenius iteration and residue field degrees are lcm”.
  Eight hits, including the finite-field Frobenius order theorem, no combined match.
- `msearch.py loogle`, query
  `IsoAlgebra, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, Module.finrank_mul_finrank`.
  Zero hits; `IsoAlgebra` unknown to this Mathlib-only index.
- `msearch.py grep`, query `constantExtension|cyclicReturn|restriction.*Weil`.
  Five unrelated function-field constant-extension hits; no statement match.
- `msearch.py leansearch`, query “Weil sheaf restriction along finite field extension
  is Frobenius iterate”. Eight hits on ordinary Frobenius maps, no Weil restriction
  or residue compositum theorem.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for `constantExtension`,
  `pullbackReturn`, `returnResidue`, and iterated Weil structures found the above
  canonical constant-extension helpers and the stronger parent theorem, which
  were read and reused. The node id has no upstream Lean hit. Searches for all new
  declaration names in both roots and `dag/lean_names_upstream.json` found none.

Sources opened: Deligne PDF pp.151–152 (PDF pages 16–17) with `pdftotext`;
the paragraph after (1.1.10) explicitly decomposes the geometric scheme by the
finite-field embeddings, and (1.1.8) specifies the residue-extension power rule.
Also read the current blueprint `literature/blueprint/latest/blueprint/
sec-deligne-laumon-general/sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`.
There is no statement correction or STATEMENT-DISPUTED flag.

Validation: `scompile.py Q16 lem-zl-constant-extension-pullback-return-residue
<module>` compiled both its sandbox probe and final library-module form cleanly,
with no errors or warnings. Every variable and both universes are explicitly bound;
`autoImplicit` is false. All lines are at most 100 characters.

## Second reading by Q16

This is the worker's own second pass, not a claim of a second agent review: the
dispatcher explicitly forbids starting other agents. The maintainer supplies the
independent review after delivery. I reread the node and final file side by side.
The positive extension degree, separate coefficient universe, finite-type and separated
model, actual pullback and Frobenius structures all match. The restriction specification
was expanded while reading to check its naturality gives the unchanged morphism map;
its iterate uses m-1 only because that existing definition indexes the mth power by m-1.
The two normalization equations were checked for types and orientations: the adjacent
arrow runs from coordinate j to i, and the full return runs from the new Frobenius
pullback of coordinate zero back to coordinate zero. Hence identities on the intermediate
arrows force exactly the stated final arrow. The resulting isomorphism is a natural
isomorphism of Weil sheaves before direct image. For residues I checked that R is the
degree over k₀, f uses the projection residue map, and the quotient equivalence extends
the actual tensor map, retaining both factor maps. The lcm, both expressions for f,
generation and cardinality clauses are all present. No mismatch or change was found.


## New nodes

`def-zl-constant-extension-sheet-pullback-data` owns the existing declarations
`WeilConjectures.constantExtensionSheetPull`,
`WeilConjectures.constantExtensionSheetPullAt`, and
`WeilConjectures.constantExtensionReturnComparison` in
`Sheaf.Paper.ConstantExtensionWeilHeartEquivalence`. Its `existing: true` record
has no `file`; no module or declaration is copied. The first is actual derived
pullback along the distinguished sheet j, the second along H^i j for every i<m,
and the third is the specified natural return isomorphism
Lg_m^* Lj^* M ≅ Lj^* L(H^m)^* M. The two normalized compositors and the equality
j g_m = H^m j are exactly the factors of the existing definition. The node states
all finite-field, coefficient, finite-type, separatedness and positive-degree
hypotheses, and cites the existing nodes for every input notion. Its source is
Deligne, paragraph after (1.1.10), p.152, and the already specified integral
pullback normalization. It asserts no k-linearity of semilinear sheet coordinates.

Searches before adding this owner: `blueprint_refs.py search
constantExtensionSheetPull` returned zero blueprint nodes; `rg` over all DAG nodes
found the three declarations recorded only by the downstream theorem
`lem-zl-constant-extension-weil-heart-equivalence`. `rg` in Mathlib, upstream
`WeilConjectures`, and the upstream declaration index found no hits. `rg` in
`lean/Sheaf` found exactly the existing definitions and their uses in the owning
module. `msearch.py leansearch` on semilinear sheet pullback and return gave eight
unrelated semilinear/Frobenius results; Loogle on `"constantExtensionSheetPull"`
and grep on the three declaration names each returned zero Mathlib hits. Their
exact search records are preserved in the new node's `mathlib_searches`.
`blueprint_refs.py ancestor` confirmed `thm-zl-real-mixed-by-curves`; the new node's
`via` is the item followed by its existing via chain. `import_flags` is empty,
matching its reach through this item. No dependency on the downstream equivalence
theorem is added.

## Repair of returned head 0ddfbd924c62

Addressed the sole H2 return in full. The retained sandbox item was compared with
the current shared-main node: before repair their only different field was `lean`.
The accepted statement, proof, proof dependencies and all other main metadata
are retained. The return explicitly approved the mathematics and allowed the Lean
source unchanged, so the exact previously delivered module is retained.
The prescribed delivery wrapper refreshes and builds on current main.

1. Added `def-zl-constant-extension-restriction-local-data` to `stmt_deps`.
   Its recorded declaration is `WeilConjectures.ConstantExtensionRestrictionSpec`
   in `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence`, with the recorded
   `constantExtensionWeilIterate`, `constantExtensionRestrictionComparison`,
   `constantExtensionFiberPull`, `constantExtensionClosedImage`, and
   `constantExtensionResidueDegree`. The complete node statement, declaration
   record and definitions were reread. This supplies explicit DAG ownership for
   every restriction/local helper identified by the reviewer.
2. Added `def-weil-local-frobenius-trace` to `stmt_deps`. Its declaration record
   in `Sheaf.Paper.LocalFrobeniusTrace` explicitly includes
   `WeilConjectures.localClosedPointDegree` and `localPositivePower`; the degree
   definition was reread with its full signature, structure-map algebra instance
   and docstring. There is no new trace or degree definition in the delivery.
3. Added and cited `def-zl-constant-extension-sheet-pullback-data`, described above,
   with all required H12 fields and its `existing: true` record owning exactly
   the three requested sheet declarations. Citing the downstream equivalence
   theorem instead would close a DAG dependency cycle, so it is not cited.

No existing dependency node is edited. Only `lean` and the authorized additions
to `stmt_deps` change on the item. There is no statement correction: the accepted
mathematics is identical. The existing source module already publicly imports
all these declaration interfaces, so the repair needs no Lean import change.

The worker's second reading of this repair checked each new ownership edge against
its node and declaration record, and checked every field of the new definition
node against brief-stage2 §5. The three coordinate declarations agree exactly with
the new node's J_0, J_i, and rho. Neither a theorem conclusion nor an arbitrary
comparison is substituted for those definitions. The prior clause-by-clause
mathematical and edge-case reading above still applies verbatim.
