## Worker report

Stage 2, Q14: `lem-trf-normal-flat-chart-relation-removal`.
The module `Sheaf.RingTheory.NormalFlatChartRelationRemoval` states
`Hironaka.normalFlatChartRelationRemoval`, with one theorem and proof `sorry`.
No definition, proof, new node, or dependency-module repair is introduced.
The mathematical statement, source, proof, proof dependencies and accepted Q37
stage-1 review are retained. The item records the existing owners of its chart,
order, minimal-family, initial-ideal and initial-form definitions in stmt_deps.
The returned theorem-node citation is replaced by the landed definition node
`def-trf-adic-initial-ideal-generator-degrees`. The initial-form and coordinate
relations owners are also cited, as advised by the reviewer. Only ownership
citations are added to the statement text; no mathematical clause is changed.
No copy of those definitions is made.

The inherited BLOCKED ending concerned stage-1 preflight on an unchanged item.
The current node is split with no Lean record; coord/queue.tsv assigns stage 2.
The stage-handoff paragraph of the current brief explicitly permits this work.
This repair starts from the retained packet returned at immutable head
739a52a76858. I did not reopen or modify the accepted split.

Source read: Hironaka, Certain numerical characters of singularities,
J. Math. Kyoto Univ. 10 (1970), pp.176–181, (19.1)–(20.12), especially
(20.3), (20.6)–(20.7), and (20.12). I opened the original 37-page scan at
https://scispace.com/pdf/certain-numerical-characters-of-singularities-18d51ii5bz.pdf.
The inherited ILO document is ancestor motivation, as the node already explains.
No replacement Stacks tag is claimed.

### Hypotheses and clause correspondence

1. The nonzero commutative regular local ring is `{T : Type u} [CommRing T]
   [IsRegularLocalRing T]`. Mathlib's regular-local class extends Noetherianity
   and localness, and `IsLocalRing` extends `Nontrivial`; no zero ring is admitted.
   `IsLocalRing.ResidueField T` is the literal quotient by its maximal ideal.
2. The parameters are `x : Fin (r+1) → T` and `y : Fin s → T`, with natural
   `r s`. `hparams` is the recorded regular-system-of-parameters predicate on
   `List.ofFn x ++ List.ofFn y`. `Ideal.span (Set.range x)` is P.
3. The original ideal a is named `b : Ideal T`, with `hb : b ≤ P`.
   R is literally `T ⧸ b`, and I is `P.map (Ideal.Quotient.mk b)`.
   `hflat` asserts `Module.Flat (R ⧸ I) (Ideal.associatedGraded I)` for the
   published degree-zero action. The scalar ring is R/I, canonically T/P;
   this is the same A as the node, not an independent algebra or an extra map.
   The maximal ideal m of R is its inherited local maximal ideal M/a.
   The descriptive S=G tensor_A k is determined by these data and appears in
   no hypothesis or conclusion, so it needs no independent binder or premise.
4. The polynomial ring B is `MvPolynomial (Fin (r+1)) (ResidueField T)`.
   `IsHomogeneous (d i)` is total-degree homogeneity, so every X has degree one.
   No additional standard-graded structure is supplied or assumed.
5. `hred : IsReduced (T ⧸ b)` and `hmin`, quantifying over Mathlib's
   `minimalPrimes (T ⧸ b)`, retain reducedness and the condition that no minimal
   prime contains the image of P.
6. The blowup-chart point is `z : PrimeSpectrum (chartRing I xbar0)`.
   This uses the actual chart subalgebra in R[1/xbar0], not a polynomial
   presentation in which xbar0 could still have torsion. `hz` says contraction
   of its prime to T equals M; equivalently it lies over m=M/a in Spec R.
   The affine chart's prime represents precisely a point in the indicated
   open of the blowup; its local ring is the localization at that prime.
7. `ParameterChart x` is the published quotient D_T. Its ratio variables are
   nonzero labels in Fin (r+1), equivalent to 1,...,r. The defining relations
   are x_i-x_0 t_i; negating them gives the node's x_0 t_i-x_i and the same ideal.
   `ι,hι` specify the ambient chart map on every coefficient and variable;
   `ρ,hρ` do the same for the quotient chart map. These are canonical maps
   specified on generators, not arbitrary homomorphisms. Their injectivity
   and surjectivity in this parameter situation are consequences, not extra
   assumptions. `LocalChart ρ z` is literally D_T localized at comap ρ z.
   Its regular-local instance is exactly the explicit regularity hypothesis.
   `transformIdeal ρ z` is the kernel of `Localization.localRingHom` into
   the quotient chart localized at z, the affine-chart description of R_z.
8. M' is `IsLocalRing.maximalIdeal (LocalChart ρ z)`.
   `exceptionalIdeal x y (PrimeSpectrum.comap ρ z)` is exactly H=(x_0,y)T'.
   The prime `p` is in the polynomial ring on the surviving ratio labels over k.
   `hp` equates its inverse image under coefficient reduction with the
   inverse image of p' in the polynomial presentation of D_T. This is exactly
   reduction of p' modulo M D_T. L is `Localization.AtPrime p.asIdeal`,
   and its maximal ideal is N=pL. The chart presentation then identifies
   T'/H with L. This identification is determined by the presentation and hp;
   no independently chosen isomorphism or quotient is assumed.
9. The coordinate map `χ` has source k[X,Y] and target the published gr_M T.
   `hχ : IsParameterGradedMap x y χ` fixes it on constants and all X,Y
   generators. For regular parameters this is the canonical coordinate
   identification, so quantifying over its generator-specified realization
   neither changes the rings nor assumes a new coefficient field in T.
10. `m,hm` retain m≥1. `f,d,φ` are indexed by `Fin m`, so index i corresponds
    to paper index i+1. `hd : Monotone d` is the ordered degree condition;
    `hdpos` retains d_i≥1. `hf` says f_i∈a, f_i∈P^d_i and
    `adicOrder M (f i) = d i`. Natural d_i embedded in ENat expresses finite
    exact order. `hφ` states both homogeneity and equality with the actual
    degree-d_i initial class after renaming X into X,Y.
11. `hbasis` uses the published `IsMinimalGeneratingFamily` and
    `adicInitialIdeal M b`. The latter is constructed from initial classes of
    b∩M^n in every degree and is the kernel gr_M T → gr_m R. It is not a
    new definition of that kernel. The family contains only the pure X forms
    renamed into k[X,Y], as required; no Y-dependent generators are allowed.
12. `g,hg` use `IsDividedElement`: a representative h in the actual ambient
    chart satisfies ι(h)=f_i/x_0^d_i in T[1/x_0], and its localization is g_i.
    This preserves division before passage to R and permits zero divisors in R.
13. `a : Fin m` represents the prefix length called b in the node, so
    0≤a.val<m. The threshold called d in the node is named `e : ℕ` with
    `he : 1 ≤ e`. `hdegree` says d_j≤e before a and e≤d_i from a onward.
14. The earlier corrected elements and corrections are named `q,w`.
    `hearlier` applies only to `j<a`, corresponding to paper j≤b.
    Its four clauses are: `InOrderSpace` (dehomogenized φ_j lies in N^d_j,
    together with its already required homogeneity); q_j=g_j-w_j;
    w_j∈H*prefixIdeal g j; and exact finite M'-order d_j for q_j.
    Values of q,w at indices ≥a are unconstrained and occur in no ideal or
    conclusion. They only extend the finite earlier family by arbitrary zeros.
15. `prefixIdeal q a` is J=(q_j:j<a), and `hjet` is exactly
    a'≤J ⊔ M'^e. The conclusion is
    `J ⊓ (H ⊔ M'^e) ≤ H * J ⊔ M'^e`. In the lattice of ideals, sup is
    ideal sum, inf is ideal intersection, and * is ideal product. All of
    these ideals live in the same actual ring T'=LocalChart ρ z.

### Dependency declarations read and used

- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`, the full finite-list predicate.
- `WeilConjectures.RingTheory.AssociatedGradedRing`:
  `Ideal.associatedGradedPiece`, `Ideal.associatedGraded`, and its canonical
  `associatedGradedAlgebra` action from the quotient by the filtration ideal.
- `Sheaf.RingTheory.PermissibleBasisChartData`: `Hironaka.ParameterChart`,
  `IsAmbientChartMap`, `IsQuotientChartMap`, `residuePolynomialMap`,
  `InOrderSpace`, `IsDividedElement`, `IsParameterGradedMap`, `LocalChart`,
  `transformIdeal`, `originalToLocal`, `exceptionalIdeal`, `prefixIdeal`.
  I read their complete signatures and definitions. This module imports the
  recorded coordinate quotient rather than constructing another chart.
- `Sheaf.RingTheory.LocalStandardBasisInvariants`: `Hironaka.adicOrder`
  and `IsMinimalGeneratingFamily`; both are reused transitively via chart data.
- `Sheaf.RingTheory.ProjectiveConeHilbertStandardDegrees`:
  `Hironaka.adicInitialIdeal`, the concrete initial ideal used by hbasis, owned
  by `def-trf-adic-initial-ideal-generator-degrees` (existing:true, Q37).
  No conclusion of `lem-trf-projective-cone-hilbert-standard-degrees` is used.
- `Sheaf.AlgebraicGeometry.NodalLocalTangentData`:
  `AlgebraicGeometry.NodalLocal.initialForm`, the canonical summand inclusion,
  owned by `def-sfb-nodal-tangent-comparison-data`.
- `Sheaf.AlgebraicGeometry.PermissibleCoordinateChart`:
  `AlgebraicGeometry.PermissibleCoordinateChart.relations`, owned by
  `def-trf-permissible-coordinate-chart-ring`, used explicitly in hp.
- `WeilConjectures.Blowup.Affine.ChartAlgebra`:
  `AlgebraicGeometry.AffineBlowup.chartRing` and `chartFraction`.
- Mathlib: `IsRegularLocalRing` and `IsLocalRing.ResidueField`;
  `Module.Flat` (also read the recorded `RingHom.Flat` equivalence);
  `MvPolynomial`, `MvPolynomial.IsHomogeneous`, `Localization.AtPrime`,
  `PrimeSpectrum`, `minimalPrimes`, ideal span/map/comap/powers/lattice operations.
  The ring clause of def-weil-regular-scheme is the recorded Mathlib match,
  not its scheme-only wrapper `IsRegularScheme`, which I also opened.
  The residue-field wrapper `Scheme.residueField` likewise reduces to the
  local-ring quotient used here. `AlgebraicGeometry.AffineBlowup` is Proj of
  the Rees algebra; the point and local ring are expressed on its specified
  affine chart. The ordinary Spec and standard-graded-algebra declarations
  were read but need no extra hypotheses in this algebraic chart statement.

Both non-definition proof inputs `lem-trf-normal-flat-initial-coefficient-lifting`
and `lem-trf-projective-order-leading-syzygies` have no Lean record or Mathlib
match on the read base. They are carried by name in the complete theorem
proof docstring; no unrecorded proof dependency module is invented. The
recorded chart definition is already a public transitive import. No import
of the downstream one-step theorem is used, preventing a dependency cycle.

### Searches and edge cases

Executed four fresh searches with the prescribed `batch2/msearch.py`,
recorded by that tool in searches.jsonl:

- LeanFinder: `Normally flat blowup chart exceptional ideal relation removal modulo finite maximal ideal powers`.
  Eight hits, chiefly Weierstrass division and ramification quotient powers;
  no matching intersection theorem.
- Loogle: `"Ideal", "inf", "pow"`. Twelve hits, chiefly Krull intersection
  and Artin–Rees; none has the chart hypotheses or the finite-jet conclusion.
- grep, Mathlib/RingTheory: `normal.?flat|relation.?removal|exceptional.*relation`.
  Zero hits.
- LeanSearch: `Ideal intersection exceptional ideal finite jets normally flat blowup`.
  Eight hits, chiefly ideal intersection membership, zero loci and localization
  of an intersection; none asserts the relation-removal inclusion.

I also ran rg of WeilConjectures and Sheaf for normal flatness, Hironaka,
finite jets, initial forms, regular systems of parameters and the exact item id;
searched dag/lean_names_upstream.json for the item and intended theorem name.
No existing item theorem was found. The searches did find the published parent
`PermissibleStandardBasisOneStep` and its shared definitions, which are reused.
The theorem is not redeclared under a different name in the published library.

Edge cases were checked before drafting: a.val=0 gives J=0 and leaves all
correction conditions empty. e=1 has no order-raising stages, and positive
orders put every earlier q in M'. r=0 has an empty ratio-variable type,
whose polynomial ring is k; s=0 has no transverse parameters. Repeated degrees
are permitted by Monotone, and the non-strict inequalities retain the threshold
equality cases. m=1 necessarily has an empty prefix. Arbitrary prime p and
arbitrary residue characteristic are retained, including non-rational and
inseparable points; no perfectness or coefficient-field section is assumed.
Zero original ideal makes the nonempty irredundant initial family impossible,
so that case is vacuous rather than silently excluded by an added premise.
The zero ring is excluded exactly as in the node. There is one explicit
universe u for the original ring and all its canonical quotients/localizations;
no universe restriction is imposed on a quantified test-object class.

Validation: scompile.py compiled the actual module in both sandbox and library
module modes successfully (3.7 s and 3.8 s). No compiler errors or unexpected
warnings were printed. Every universe and variable is explicit, with
`set_option autoImplicit false`. All theorem proofs consist of sorry only.
No statement fault or STATEMENT-DISPUTED issue was found.

## Second reading by Q14

I performed a separate rereading of the completed file against the unchanged
node and the definitions opened above. This is a second pass by the assigned
worker, not a claim that another agent reviewed it: the dispatcher explicitly
prohibits starting other agents, and the maintainer supplies the independent
review after delivery.

I checked in particular the two different uses of b: the original ideal is
Lean `b`, whereas the paper's prefix length is Lean `a.val`. Thus `j<a`
is exactly paper j≤b after shifting indices, and `a≤i` is paper i>b.
The threshold e is unrelated to the degree family d. Both parts of hdegree,
the full positive monotone degree family, and the strict prefix b<m are present.
The original reducedness and minimal-prime assumptions are retained, although
the final ideal inclusion would hide them if one looked only at its type.

I reopened IsDividedElement, LocalChart and transformIdeal: fractions are
computed in the ambient T localization, p' is comap ρ z, and the kernel map
is the canonical localized quotient chart map. Neither an arbitrary map of
local rings nor an arbitrary element satisfying only a cross-multiplied equation
replaces that construction. hp retains the polynomial-prime reduction; hχ pins
all X and Y generators. The initial ideal is the existing all-degrees initial
ideal, and the minimal family consists of the actual initial classes of f.

I checked all four earlier correction clauses and the finite-jet hypothesis
against the node. The intersection, product and two sums in the final type
are in T', with exactly exponent e. The empty-prefix and threshold-one cases
remain included. The docstring carries all five accepted proof steps, including
the use of H*a'≤HJ+M'^(e+1), and does not pretend to prove either missing
proof-input node. I replaced one draft docstring sentence with the direct
statement that the descriptive cone fibre is determined by the given rings;
no mathematical signature changed during this rereading. No mismatch found.

## Return repair: H2 at 739a52a76858

Replaced stmt_dep `lem-trf-projective-cone-hilbert-standard-degrees` with the
landed definition owner `def-trf-adic-initial-ideal-generator-degrees` and cited
that owner at the initial-ideal clause. Implemented both advisory citations:
`def-sfb-nodal-tangent-comparison-data` at the initial-form clause, and
`def-trf-permissible-coordinate-chart-ring` at the displayed chart presentation.
All three owners were checked against their current node records and the full
signatures and docstrings of adicInitialIdeal, initialForm and relations.
These are citation-only edits. The server preflight requires statement_change
for any textual statement edit, so that record and the full citer audit are
included below; no mathematical statement correction is made.

The initial saved-packet dry run passed (commit 1b66e911ba6), but did not itself
repair the independent review's ownership diagnostic. The changes above repair
that diagnostic before the final dry run and push. Against the current shared
read clone the saved packet initially differed only in lean and stmt_deps;
the repaired packet additionally adds the three explanatory statement citations.
The delivery wrapper rebases the packet onto the live server branch.

The Lean file is byte-identical to the returned packet. Its SHA-256 is
`6db3ce5784d6a68650fd2d8c82a3112bf561ef5ae8c66ac7a1d7ab38935469c2`.
The lean.statement record still exactly matches its signature. The previous
hypothesis/clause correspondence and edge-case review therefore remain valid.
A second self-check confirms that hbasis uses the initial-ideal definition,
hφ uses the canonical initialForm, and hp uses the coordinate-chart relations;
no theorem conclusion is being used as statement data.

## Statement corrected

The old statement is retained verbatim in statement_change.old_statement. Its
mathematical content is unchanged. The textual defect was missing explicit
ownership citations at the initial-ideal, initial-form and chart-presentation
clauses, as identified in the return at 739a52a76858. The three citations now
name exactly the landed definition owners; stmt_deps reflects those owners.
Source: Hironaka (1970), proof of Lemma 20, (20.3)–(20.12), pp.177–181,
the same source/place as the original node. No hypotheses or conclusions
are modified. The initial repaired-packet dry run rejected these citation
additions without a statement_change record; this record repairs that diagnostic.

Citer audit: rg -l for the exact quoted item id found the item, its two
proof-input nodes (blueprint ancestry only), and the following sole actual
stmt_deps/proof_deps citer. Each matching node was inspected; only that
last node cites the item in either dependency field.

- lem-trf-permissible-standard-basis-one-step: holds true. Proof step 6
  uses the inclusion with b=a-1 and d=d_a and supplies exactly the same
  hypotheses; ownership citations do not alter this use. The citer is not edited.
