## Worker report

The module `Sheaf.RingTheory.ArtinianFiniteResidueRestriction` states
`RingHom.artinian_finite_residue_restriction` and defines the canonical auxiliary
map `RingHom.finiteResidueRestrictionMap`. The pullback ring is Mathlib's
`RingHom.pullback`, so its elements are exactly pairs satisfying the residue-map
equality and its operations are coordinatewise.

The binders `k`, `l`, `[Field k]`, `[Field l]`, `[Algebra k l]`, and
`[FiniteDimensional k l]` render the finite field extension $k\hookrightarrow l$.
The binders `B`, `[CommRing B]`, `[IsArtinianRing B]`, `[IsLocalRing B]`, `ρ`, and
`hρ` render the Artinian local ring and its specified surjective residue map.
The first conjunct states that `ρ.pullback (algebraMap k l)` is Artinian. The
existential `hC` supplies its local-ring structure; its first conjunct says the
second projection to `k` is surjective, and the kernel equality identifies `k`
with the residue field. The next conjunct states injectivity of the first
projection to `B`.

The final universal clause binds an Artinian local `B'`, its identified residue
map `ρ'` and surjectivity, and a surjection `q : B' →+* B` inducing the identity
on the identified residue field via `hρq : ρ' = ρ.comp q`. It states that the
canonical map on pullbacks is surjective and that its second-coordinate map is
exactly the identity-compatible projection `ρ'.pullbackSnd`.

The module uses `RingHom.pullback`, `RingHom.pullbackFst`,
`RingHom.pullbackSnd`, `RingHom.restrict`, `RingHom.prodMap`, and
`IsLocalRing.maximalIdeal` from Mathlib. The proof plan imports the already
recorded declarations `semilocal_restriction_length` from
`Sheaf.RingTheory.SemilocalRestrictionLength`; the Artinian self-length and
module-length notions are represented by Mathlib's `isArtinianRing_iff_isFiniteLength`
and `Module.length` (the corresponding DAG nodes have Mathlib matches).

Edge cases checked against the source: `k = l` gives the identity pullback;
`B = l` gives `C = k`; the zero ideal and square-zero Artinian examples retain
locality; the injectivity argument uses that a field algebra map is injective;
and the finite-dimensional hypothesis is required for the length argument.
For a surjection, the compatibility equality makes the source pullback use its
specified residue map, while the unchanged second coordinate gives the identity
on `k`.

Searches made: `msearch.py ... leanfinder "Artinian local ring pullback along a finite extension of residue fields is Artinian local and preserves surjections"` (no exact match; only residue-field and Artinian-fibre results); `msearch.py ... leansearch "An Artinian local ring with residue field l pulled back along a finite field extension k to l is Artinian local with residue field k"` (no exact match); `msearch.py ... loogle "RingHom.pullback"` (Mathlib declarations `RingHom.pullback`, `pullbackFst`, `pullbackSnd`, locality and surjectivity lemmas); `msearch.py ... grep "fiberProduct|fibreProduct|pullback.*Subring|subring.*pullback" RingTheory` (Mathlib `Mathlib/RingTheory/LocalRing/Pullback.lean`); and `rg` over `lean/WeilConjectures` and `lean/Sheaf` (no project declaration of this theorem).

No `STATEMENT-DISPUTED` issue was found. The theorem proof is intentionally `sorry` at stage 2; the auxiliary map has real data.

## Second reading by Q65

I reread the node and the Lean signature clause by clause. The field extension,
Artinian local hypotheses, specified residue maps, pullback ring, locality/residue
kernel, injective first projection, and the surjective pullback map are all
present. The compatibility equality explicitly expresses that the surjection
induces the identity on the identified residue field. No proof is present beyond
the required `sorry`.
