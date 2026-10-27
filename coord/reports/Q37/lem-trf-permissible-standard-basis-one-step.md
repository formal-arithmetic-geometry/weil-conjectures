## Worker report

Item: lem-trf-permissible-standard-basis-one-step. Group Q37, stage 2.

The delivery states Hironaka.permissibleStandardBasisOneStep in
Sheaf.RingTheory.PermissibleStandardBasisOneStep, with sorry as its sole proof.
Two definition nodes supply ideal-adic order, minimal-family predicates and
coordinate constructions, with real data and no additional postponed theorems.
A third definition-only node owns the reused existing initial-ideal and degree-sequence
constructions through an existing:true record, without adding a Lean file.
The existing Hironaka.nuStar and adicInitialIdeal are imported and reused. The item's
accepted natural-language statement, seven proof steps and proof dependencies
are unchanged. Only its lean record and added statement dependencies change. The new
def-trf-adic-initial-ideal-generator-degrees node owns the reused invariants;
the projective-cone theorem is not a statement dependency. No statement correction or disputed statement is needed.

The inherited BLOCKED ending described a stage-1 unchanged-item refusal after
Q33's accepted split. The current standing brief, section 0 (stage handoff,
2026-10-22), explicitly permits recording Lean for such a split in stage 2.
The node currently has no lean record and queue.tsv assigns stage 2. I therefore
continued with deliver2.py, preserving the accepted split.

Hypothesis-by-hypothesis and clause-by-clause reading:

| Node | Lean rendering |
| --- | --- |
| Nonzero commutative regular local T | CommRing T and IsRegularLocalRing T; the latter already implies Nontrivial T, IsLocalRing T and IsNoetherianRing T. An initially explicit Nontrivial instance was removed following the overlapping-instance warning. |
| k=T/M | IsLocalRing.ResidueField T, whose definition is exactly T / maximalIdeal T. The degree-zero graded action uses the quotient type explicitly to resolve its wrapper. |
| r,s>=0 and ordered regular parameters x0,...,xr,y1,...,ys | r s : Nat, x : Fin (r+1) → T, y : Fin s → T, hparams : IsLocalRing.IsRegularSystemOfParameters (List.ofFn x ++ List.ofFn y). |
| P=(x0,...,xr), b subset P, R=T/b, I=P/b, A=T/P=R/I | Ideal.span (Set.range x), hb, T ⧸ b, the map of P under Ideal.Quotient.mk b, and its double quotient. A is represented by the canonically identical R/I throughout flatness; no unrelated scalar action is supplied. |
| gr_I R flat over A | hflat : Module.Flat (R ⧸ I) (Ideal.associatedGraded I), using the existing canonical associatedGradedAlgebra instance. |
| S=G tensor_A k and B=k[X0,...,Xr], degree-one variables | The polynomial type of φ is MvPolynomial (Fin (r+1)) (IsLocalRing.ResidueField T); homogeneous degrees use IsHomogeneous. S is auxiliary notation in the node and appears in no hypothesis or conclusion; it adds no condition and needs no binder. No alternative S or tensor operation is introduced. |
| R reduced; no minimal prime contains I | hred : IsReduced (T ⧸ b); hmin quantifies q in minimalPrimes (T ⧸ b) and negates I ≤ q. Mathlib minimalPrimes means primes minimal over zero. |
| z belongs to the x0-chart of Bl_I Spec R and lies over m | z : PrimeSpectrum (AffineBlowup.chartRing I x0bar), with hz asserting that its contraction along T→R→C is M. This is exactly a point in Spec C, the stated affine open chart. A point of this open gives its blowup point and conversely; using the open chart does not restrict the allowed point. Its local ring is Localization.AtPrime z.asIdeal. |
| D_T=T[t]/(x0 ti-xi) | ParameterChart x is an abbreviation of the already published PermissibleCoordinateChart.Chart x univ 0. Its relations are xi-x0 ti, the negatives of the displayed relations and hence generate exactly the same ideal. RatioLabel r retains the nonzero original labels instead of relabelling them 1,...,r. |
| D_T embeds in T[1/x0] before localization | ι and hι specify exactly the coefficient inclusion and each fraction xi/x0. A hom on the quotient is fixed by these generator equations; it is not an unconstrained map. Regularity of the parameter system gives the usual embedding. No injectivity or existence assertion was added as a hypothesis. |
| D_T→R[I/x0bar], p' inverse image of z | ρ with hρ fixes the quotient on every coefficient and the corresponding fraction on every ratio generator. p' is PrimeSpectrum.comap ρ z, not an independently chosen prime. These equations uniquely fix the canonical map. |
| T' regular local, R_z blowup local ring, b'=kernel | LocalChart ρ z is Localization.AtPrime p'.asIdeal, supplied IsRegularLocalRing exactly as assumed in the node; transformIdeal ρ z is the kernel of Localization.localRingHom p' z ρ rfl to C_z. Thus it uses the actual canonical localized map. |
| E and ν* | The existing adicInitialIdeal (IsLocalRing.maximalIdeal T) b spans precisely the degree-n classes of b∩M^n. The existing nuStar uses adicGrade, gradedGeneratorMultiplicity and generatorDegreeSequence: the quotient E_d / (sum of positive-degree graded pieces times E_{d-j}), its residue-field dimension and the sorted padded sequence. This directly implements the multiplicity formula in the item. Both are reused from Sheaf.RingTheory.ProjectiveConeHilbertStandardDegrees. |
| p obtained from p' modulo M, L=k[t]_p, N=pL | p is a PrimeSpectrum of the residue polynomial ring; hp equates its inverse image in T[t] with the inverse image of p' along the presented quotient. This exactly specifies the quotient prime. InOrderSpace uses Localization.AtPrime p.asIdeal and its maximal ideal, canonically pL. |
| U_d={φ homogeneous degree d:φ(1,t)/1 in N^d} | InOrderSpace combines φ.IsHomogeneous d with membership of algebraMap (MvPolynomial.dehomogenizeX k 0 φ) in the dth power of that maximal ideal. The published dehomogenizeX fixes X0 to 1 and preserves all other labels. |
| order supremum; M'; H=(x0,y)T' | adicOrder is the supremum in ENat of all ideal powers containing the element. IsLocalRing.maximalIdeal (LocalChart ρ z) is M'. exceptionalIdeal is the map of span ({x0} ∪ range y) under T→D→T'. |
| m>=1, f_i in b, sorted positive orders, f_i in P^di | m, hm, f, d, hd : Monotone d, hdpos and hf, with hf explicitly containing all three membership/order clauses. |
| φ_i initial forms in k[X]_di inside gr_M T=k[X,Y] | φ type, hφ with IsHomogeneous and the equality to the already published NodalLocal.initialForm. χ and hχ fix the graded coordinate map on all residue coefficients and all x and y parameters; no coefficient field T←k is assumed, and mixed characteristic is retained. Polynomial rename Sum.inl includes k[X] into k[X,Y]. |
| φ_i minimal homogeneous generators of E(T,b) | hbasis : IsMinimalGeneratingFamily (adicInitialIdeal (IsLocalRing.maximalIdeal T) b) (fun i ↦ χ (rename Sum.inl (φ i))). Together with hφ this is exactly minimal homogeneous generation, allowing repeated degrees. |
| g_i=f_i/x0^di in T', defined before localization | g and hg : IsDividedElement. This requires an actual element of D whose image under ι is the fraction in T[1/x0], followed by its image in D_p'. It neither divides by x0 in T' nor assumes x0 was a nonzerodivisor in R. This uniquely specifies the node's divided element. |
| a in {1,...,m} | a : Fin m, with the paper's index shifted down by one everywhere. |
| for j<a: ν*_j=di, φ_j in U, and earlier exceptional correction of exact order | hearlier quantifies all j<a and contains respectively the nuStar equality at j.val, InOrderSpace, and ∃ w ∈ H * prefixIdeal g j with adicOrder M' (g j-w)=d j. |
| ν*_a>=d_a | hnext : (d a : ENat) ≤ nuStar (transformIdeal ρ z) a.val. Infinite entries are permitted. |
| coefficients c_j in P^(da-dj), and all c_j/x0^(da-dj) belong to T' | Existential c and γ with the first conjunct for all j<a: membership in the required power and IsDividedElement giving exactly γ_j. Values at indices outside the prefix are ignored and can always be extended by zero. The subtraction Nat uses is valid because hd gives d_j≤d_a. |
| v in H(g1,...,g_{a-1})T' | Second conjunct v ∈ exceptionalIdeal ... * prefixIdeal g a. |
| f_a*=f_a-sum c_j f_j | correctedGenerator f a c, the finite sum over precisely those Fin m indices less than a. |
| g_a*=g_a-sum (c_j/x0^(da-dj))g_j=f_a*/x0^da | correctedGenerator g a γ and the penultimate IsDividedElement conjunct express both formulas in the actual ambient fraction ring and then T'. |
| ord_M f_a*=d_a | Third conjunct uses adicOrder M (correctedGenerator f a c)=d a. |
| in_M f_a* belongs U_da | Existential ψ with InOrderSpace r p (d a) ψ, and equality under χ∘rename to the actual degree-d_a class of the corrected original. The preceding exact-order clause makes this its initial form, not a lower-degree zero class. |
| ord_M'(g_a*-v)=d_a | Last conjunct, with the exact correctedGenerator, v, M' and degree. |
| a=1: empty sums and zero earlier ideal | a=0 in Fin m; the filtered sum is empty and prefixIdeal spans the empty set. Membership of v in H*0 forces v=0. |

Definition and module dependencies read and reused:

- def-weil-regular-scheme: its mathlib_match ring clause IsRegularLocalRing,
  Mathlib.RingTheory.RegularLocalRing.Defs. Its scheme-only lean binding is not
  used because the present node concerns a ring, not a regular scheme.
- def-weil-residue-field: the ring residue field underlying the recorded
  Scheme.residueField, Mathlib.RingTheory.LocalRing.ResidueField.Defs; no new
  residue-field notion. Read Scheme.residueField and residueFieldMap too.
- def-weil-pbc-regular-system-of-parameters:
  WeilConjectures.RingTheory.IsRegularSystemOfParameters,
  IsLocalRing.IsRegularSystemOfParameters, including its empty-list convention.
- def-weil-pbc-associated-graded-ring:
  WeilConjectures.RingTheory.AssociatedGradedRing, Ideal.associatedGraded,
  associatedGradedPiece, associatedGradedAlgebra, and canonical DirectSum.of.
- def-weil-pbc-flat-ring-map: Mathlib.RingTheory.RingHom.Flat and
  Mathlib.RingTheory.Flat.Basic, Module.Flat. No private flatness predicate.
- def-weil-pbc-module-tensor-product: mathlib_match TensorProduct; read its
  definition. The auxiliary S is unused, so the statement does not need a
  redundant tensor-product binder or an added flatness assertion for S.
- def-weil-pbc-mv-polynomial-ring: MvPolynomial, eval₂Hom and rename;
  Mathlib.Algebra.MvPolynomial.Basic/Eval/Rename, plus IsHomogeneous.
- def-pc-standard-graded-algebra: read GradedAlgebra.IsStandard and its degree
  pieces, WeilConjectures.RingTheory.GradedAlgebra.Standard. The polynomial
  degree convention is already exactly Mathlib's IsHomogeneous, so no extra
  IsStandard instance is assumed.
- def-weil-affine-spectrum and def-nagata-affine-blowup: read Spec and
  AffineBlowup and its chart, respectively Mathlib.AlgebraicGeometry.Scheme and
  WeilConjectures.Blowup.Affine.Defs. The chosen chart is represented by its
  ordinary PrimeSpectrum, so no independent blowup point or stalk model is needed.
- def-nagata-blowup-chart-ring: AffineBlowup.chartRing and chartFraction,
  WeilConjectures.Blowup.Affine.ChartAlgebra, with its explicit subalgebra of the
  away localization, not an arbitrary presented quotient of R.
- def-weil-pbc-localization-at-prime: Localization.AtPrime,
  Mathlib.RingTheory.Localization.AtPrime.Basic, and Localization.localRingHom.
- Additional landed constituent nodes used through the new definitions:
  def-sfb-nodal-tangent-comparison-data, NodalLocal.initialForm in
  Sheaf.AlgebraicGeometry.NodalLocalTangentData; and
  def-trf-permissible-coordinate-chart-ring, PermissibleCoordinateChart.Chart
  and ratio in Sheaf.AlgebraicGeometry.PermissibleCoordinateChart.
- MvPolynomial.dehomogenizeX is reused from the published
  WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous, not defined again.

None of the four non-definition proof dependencies currently has a usable lean
record; no unused or cyclic proof import is added. The seven-step proof in the
item and in the main theorem docstring records their exact eventual uses.

Edge cases checked: the first index has the empty earlier family; s=0 retains
only the exceptional coordinate in H; r=0 gives no ratio variables, residue
polynomial ring k, and U_d=0 for d>0. Equal adjacent degrees permit constant
coefficients (P^0=T). The zero initial ideal gives the empty minimal family and
an all-infinity sequence, but cannot satisfy the theorem's nonempty minimal
family hypothesis. Zero elements have infinite order, so positive finite d_i
correctly exclude them. No perfectness, rationality, equicharacteristic, or
coefficient-field assumption occurs. At an inseparable prime (t^p-c), the
polynomial X1^p-cX0^p has dehomogenized order one and is therefore excluded from
U_p; the definition retains the necessary U condition. If x0bar is zero, its
chart is the zero ring with no prime z, correctly making that chart empty.
All rings and finite polynomial/quotient/localization constructions remain in
an arbitrary universe u; no additional universe equality is imposed.

Searches: msearch.py leanfinder for the theorem returned Weierstrass series and
preparation lemmas, no permissible correction. Loogle for Ideal/order returned
order embeddings and simple ideal lattices, not adic order. LeanSearch for the
padded initial-ideal degree sequence returned homogeneous ideals and ordinary
finite homogeneous algebra generators, not nuStar. A second LeanFinder phrasing
returned leading coefficients, Rees algebras and homogeneous-localization
spanning lemmas, still no match. LeanSearch for polynomial chart/divided/order
data returned ordinary homogenization and homogeneous localizations, not the
normalized data here. Loogle for MvPolynomial/IsHomogeneous/order returned zero
hits. Mathlib grep for nuStar/Hironaka/initialIdeal/initialForm returned zero;
source and Sheaf rg searches located the existing initialForm, chartRing,
coordinate quotient, and dehomogenizeX reused above, but no theorem or full new
notion. The explicit queries and verbatim msearch result records are carried
in each new node's mathlib_searches. The whole DAG was searched for these
notions and blueprint_refs.py search 'standard basis' returned only unrelated
relative affine space and categorical trace. The original searches missed the concurrently landed ProjectiveConeHilbertStandardDegrees module. The return identified this overlap; the repair now imports its definitions directly.

Source read: the cited Hironaka PDF online, §§2–3 pp.153–155 and Lemma 20 with
(19.1)–(20.12), pp.176–181; especially Remark 1 identifies the padded sorted
minimal-generator degrees used in nuStar. The source's further equality of the
next ν* entry is intentionally absent because it is not a clause of this node.

Validation: all three files compiled individually through scompile.py against
the live published build and the private dependency overlay. The only initial
issues were residue-field wrapper instance inference (fixed by explicit quotient
scalars) and redundant Nontrivial (removed). Final compilation is clean. The dry run also required the current new-node schema
field import_flags; both new nodes carry the empty list. The signature record
was corrected to retain the entire theorem through its final type, including
the internal named argument (T := T).
Every variable/universe is explicit with autoImplicit false. No data contains
sorry. The only postponed proof is permissibleStandardBasisOneStep, matching
the item's DAG node and complete proof docstring.

## New nodes

def-trf-local-standard-basis-invariants owns adicOrder,
IsMinimalGeneratingFamily and HasDegrees. Source: Hironaka §§2–3, pp.153–155.
It supplies the supremum of ideal-power membership, irredundant generation and
membership in the degree summands of the existing associated graded ring.
The originally included initial ideal and ν* constructions have been removed:
those notions are reused from ProjectiveConeHilbertStandardDegrees.lean and now
belong to the definition-only node def-trf-adic-initial-ideal-generator-degrees.
The new node has been narrowed accordingly. No invariant was renamed or copied.
Its module is LocalStandardBasisInvariants.lean.

def-trf-permissible-basis-chart-data owns the coordinate-generator map predicates,
residue polynomial map, U_d predicate, divided-element relation, canonical local
chart and transform kernel, structural map, H, prefix ideal and triangular sum.
Source: Hironaka (13.1), chart paragraph p.169 and (19.1)–(20.3), pp.176–177.
Its ParameterChart alias reuses the exact published quotient; all coefficients,
ratio classes, localizations, chart algebras and dehomogenization are reused.
The new data are their normalized combination needed to state Lemma 20, not a
second definition of a coordinate chart or homogeneous localization. Searches
listed above found only its constituent APIs, not these predicates. Its module
is PermissibleBasisChartData.lean. Neither source module asserts a theorem.

def-trf-adic-initial-ideal-generator-degrees owns the already existing plain
definitions Hironaka.gradedIdealPiece, gradedGeneratorMultiplicity,
generatorDegreeSequence, adicGrade, adicInitialIdeal and nuStar in
Sheaf.RingTheory.ProjectiveConeHilbertStandardDegrees. Its existing:true record
points to the exact nuStar signature, with all six names listed. No source is
moved, copied, or newly declared. Hironaka §2 pp.153–154 and §3 p.155 define
the initial ideal and degree multiplicities. The definition node states the
actual quotient, degree spans, initial-ideal generators, and cumulative-degree
infimum. Mathlib LeanSearch returned homogeneous-ideal APIs, LeanFinder returned
localization degrees and polynomial-order APIs, and Mathlib grep returned zero
hits. Project and DAG grep found only the existing module and theorem-node
record; blueprint_refs.py found no initial-ideal node. The new node records all
three fresh msearch results verbatim and reuses the definitions as required.

## Review status

No other worker was started, as required by the brief. The independent second
reading is the maintainer's review after delivery. The matching table above is
the author's explicit statement audit, not a claim of an independent reading.

## Repair of return L (immutable head 8fc36b4b65c1)

Point 1: removed the duplicate Hironaka.nuStar, rather than renaming it. The main
module now publicly imports Sheaf.RingTheory.ProjectiveConeHilbertStandardDegrees
and uses its existing Hironaka.nuStar in hearlier and hnext. I also removed the
parallel initialIdeal construction and use the existing Hironaka.adicInitialIdeal
directly in hbasis. The main node cites their owning landed node in stmt_deps.
The invariant helper node now records adicOrder as its principal declaration and
contains only the remaining three declarations and their notions.

I compared the retained packet with the return's listed declarations and the
current shared source, then read the current server module using scompile.py
--source. Both versions of ProjectiveConeHilbertStandardDegrees agree. Its ν*
is the item's exact indecomposable-multiplicity formula, with positive degrees
enumerated from index zero and infinity for an empty tail. In this theorem both
ambient rings are regular local, so the finite multiplicities are ordinary
residue-field dimensions. A zero ideal has zero multiplicities and an all-infinity
sequence; repeated positive degrees are repeated by their multiplicity. The
existing adicInitialIdeal uses the same DirectSum.of and Submodule.Quotient.mk
classes as the deleted construction.

The saved packet's first dry run passed, which did not resolve the independent
name-collision return. This repair changes the source and records, while retaining
the theorem's hypotheses and conclusions and all seven proof steps. The theorem
uses the published invariant construction directly; no equivalence theorem or
extra assumption was added. All three delivered files are checked separately
through scompile.py; the subsequent dry run and push use deliver2.py.

## Repair of return L (immutable head 15039e6fb241)

H2 (§2): replaced the statement dependency on
lem-trf-projective-cone-hilbert-standard-degrees with the new definition-only
node def-trf-adic-initial-ideal-generator-degrees. Read all six existing
definitions and their docstrings locally and on the server. Their bodies are
real data and do not choose anything from the theorem. The new existing:true
record lists all six declarations, including gradedIdealPiece, which the
multiplicity construction uses. No new Lean module or duplicate definition
is introduced.

§12: added def-sfb-nodal-tangent-comparison-data to both the item's and
def-trf-permissible-basis-chart-data's stmt_deps. The latter's definition text
now cites that node where it uses initialForm in IsParameterGradedMap. Read
NodalLocal.initialForm's full signature and body: it is the canonical
DirectSum.of of Submodule.Quotient.mk, matching hφ, the corrected initial
form clause, and the degree-one parameter conditions. Added
def-trf-permissible-coordinate-chart-ring directly to the item's stmt_deps
for the relations declaration in hp. The chart-data node already cites it.
Read relations and Chart in their owning module; the inverse image in hp
uses precisely that quotient map.

The advisory unused HasDegrees is retained in its existing definition node;
no Lean changes are needed for this return. All three sandbox Lean files
remain byte-identical to the returned packet (SHA256: LocalStandardBasisInvariants
df41f33418e11274548ccfc2deff8dfd34cbf6ff4da472b9cb5e1a1759b213f6;
PermissibleBasisChartData
8912c327ca96a1c09a9fd39301d96f213a1f7c642b0996aadc1a342cf17db755;
PermissibleStandardBasisOneStep
165d1f1775078f9fd8ae81d5a39d3f3f804de22d9775b25d7e30eae32eaea243).
The shared base comparison confirms the item's mathematical statement, proof
and proof dependencies are unchanged: only lean and stmt_deps differ. The
wrapper refreshes the current main base when building the delivery commit.

Self-check: reread the clause table above and the invariant definitions against
Hironaka §2–3 (pp.153–155); the new record captures the same existing data.
The empty initial ideal has all-infinity degree sequence; repeated positive
degrees retain their multiplicity; degree zero is excluded from the padded
sequence, as required for a proper ideal in a regular local ring. Infinite
vector spaces use the existing finrank convention, with no assertion of
finiteness added. The theorem still has the same regular-local hypotheses,
canonical maps, actual inverse-image primes and transform kernel, and empty
prefix behavior validated in the return. No mathematical statement correction
or disputed statement is introduced.

## Second reading by Q37

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
