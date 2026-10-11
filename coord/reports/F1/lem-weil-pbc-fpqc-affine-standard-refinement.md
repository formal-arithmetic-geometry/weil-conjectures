## Worker report

The module `Sheaf.AlgebraicGeometry.FpqcAffineStandardRefinement` states
`AlgebraicGeometry.Scheme.exists_fpqc_affine_standard_refinement`, with `sorry` as its
only proof. No definition, extra node, dependency module, or statement correction is needed.

Hypothesis and conclusion correspondence:

- The commutative ring R and affine base T = Spec(R) are `R : CommRingCat.{u}` and
  `Spec R`. Bundling R includes its commutative-ring structure, without assuming nonzero R.
- The arbitrary set I, schemes T_i, and morphisms f_i are `{I : Type v}`,
  `T : I → Scheme.{u}`, and `f : ∀ i, T i ⟶ Spec R`. The index universe v is independent
  of the scheme universe u; there is no countability or finiteness hypothesis on I.
- The fpqc-covering hypothesis is
  `hf : Presieve.ofArrows T f ∈ fpqcPrecoverage (Spec R)`. This uses the dependency's
  recorded definition, and includes flatness of every member and the finite-open
  condition. Mathlib uses quasi-compact opens rather than affine opens: these admit
  finite affine covers, so this is the same covering notion, as the dependency records.
- The finite set J is represented by `Fin n`, with `∃ (n : ℕ)`; every finite set has
  such a presentation. No nonemptiness is imposed.
- The index selection a is `a : Fin n → I`; repeated original indices are allowed.
- The selected opens are `V : ∀ j, (T (a j)).Opens`, with
  `∀ j, IsAffineOpen (V j)`. An open is the actual open subscheme of the given member.
- The rings A_j are the canonical global-section rings of `(V j).toScheme`.
  `IsAffineOpen (V j)` means `IsAffine (V j).toScheme`; Mathlib's
  `Scheme.isoSpec` identifies it with the spectrum of its global-section ring.
  Thus the clause V_j = Spec(A_j) is expressed by affineness, using the canonical
  coordinate ring rather than adding arbitrary choices of rings and identifications.
- The induced R → A_j is
  `((ΓSpecIso R).inv ≫ ((V j).ι ≫ f (a j)).appTop).hom`: first identify R with
  global sections of Spec R, then pull back along the selected open's map to Spec R.
  `RingHom.pi` forms precisely the map into the dependent product of these rings.
  `.FaithfullyFlat` is the node's full conclusion, using `RingHom.FaithfullyFlat`.
  The node does not separately ask for image coverage in its conclusion; faithful
  flatness of the product implies it. There is no extra conclusion imposed.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme`. `IsAffineOpen`, from
  `Mathlib.AlgebraicGeometry.AffineScheme`, supplies the affine-open terminology already
  included in that node. These are transitively imported by the fpqc module.
- `def-weil-pbc-fpqc-covering`: `AlgebraicGeometry.Scheme.fpqcPrecoverage`, from
  `Mathlib.AlgebraicGeometry.Sites.Fpqc`; read its definition and the defining
  `propQCPrecoverage` in `Sites.QuasiCompact`.
- `def-weil-pbc-faithfully-flat-ring-map`: `RingHom.FaithfullyFlat`, from
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`; its definition is faithful flatness of
  the target module via the given ring homomorphism.

Edge cases: `n = 0` is allowed, including when I is empty; the empty product is the
zero ring, faithfully flat over the zero ring. When R is nonzero, an empty covering
cannot satisfy the hypothesis, and an empty product cannot be faithfully flat over R.
The opens may themselves be empty. No distinctness of a(j), field, characteristic,
Noetherian, or quasi-compactness hypothesis on the individual T_i is imposed.

Searches (2026-10-11):

- `msearch.py leanfinder`: "fpqc covering of affine scheme admits finite affine opens
  with faithfully flat product of coordinate rings". Eight related results, notably
  `Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine` and
  `quasiCompactCover_iff`; none selects opens of the given family with this conclusion.
- `msearch.py loogle`: `AlgebraicGeometry.Scheme.fpqcPrecoverage`. Eight results defining
  the precoverage and proving stability/topology comparisons; no matching refinement.
- `msearch.py leansearch`: "finite affine refinement of fpqc covering with faithfully
  flat product of rings". Service unavailable (Internal Server Error).
- `msearch.py grep` in AlgebraicGeometry: `fpqc.*refin|affine.*refin|RingHom.pi`.
  Sixteen results, including product maps and open-cover affine refinements; no match.
- `rg` in `WeilConjectures` and `lean/Sheaf`:
  `fpqc.*refin|affine.*refin|lem-weil-pbc-fpqc-affine-standard-refinement`.
  Read `WeilConjectures/Mathlib/AlgebraicGeometry/Sites/Fpqc.lean`: its
  `exists_finite_affine_flat_of_mem_fpqcTopology` selects arbitrary affine schemes
  factoring through a covering sieve, not affine opens of the given family, and does
  not state the ring-product conclusion. Read the project's
  `FpqcSingletonAffineRefinement.lean`: it treats one source morphism and a coproduct
  conclusion, not this arbitrary family. Fppf refinements impose additional local
  finite-presentation hypotheses. No exact existing declaration found.

The local literature checkout is absent. Read the primary source pages instead:
[Stacks 022B](https://stacks.math.columbia.edu/tag/022B) gives the finite affine-open
condition, and [Stacks 03N0](https://stacks.math.columbia.edu/tag/03N0) uses the standard
refinement after the affine reduction. These agree with the node. The module docstring
carries all three recorded proof steps and their dependency node names. No statement
fault or disputed claim was found.

Server validation: `scompile.py F1 lem-weil-pbc-fpqc-affine-standard-refinement` on the
module completed with exit code 0 in 1.7 seconds, without errors or warnings.

## Second reading by F1

I independently read the node, its three statement dependencies, and the delivered
module. No statement correction, new definition node, or dependency module is present
or needed. No mathematical or Lean mismatch was found; the Lean and node record are
unchanged. This section is the only manual change.

Source check: the local Stacks checkout is absent. I read the primary Stacks pages
[022B](https://stacks.math.columbia.edu/tag/022B) and
[03N0](https://stacks.math.columbia.edu/tag/03N0), and the upstream raw `topologies.tex`
at `definition-fpqc-covering` and `descent.tex` at `lemma-open-fpqc-covering`
(lines 4100–4127). Definition 022B assumes arbitrary schemes and flat arrows with
finite affine-open image coverage; no finiteness, separation, nonzero-ring or field
assumption is imposed. The proof of 03N0 explicitly reduces to affine T and then
chooses a standard refinement. The node's ring-product conclusion follows from
flatness and joint coverage as its three proof steps describe.

Object/hypothesis/conclusion checklist, in node order:

1. Commutative ring R and affine base T = Spec(R): `R : CommRingCat.{u}` and
   `Spec R`. PASS: arbitrary commutative rings, including the zero ring.
2. Set I and schemes T_i: `{I : Type v}` and `T : I → Scheme.{u}`. PASS:
   unrestricted index size, with separately bound u and v.
3. Morphisms f_i:T_i→Spec(R): `f : ∀ i, T i ⟶ Spec R`. PASS: ordinary
   scheme morphisms, the recorded `Scheme.Hom` notion, with the correct target.
4. Fpqc hypothesis: `hf : Presieve.ofArrows T f ∈ fpqcPrecoverage (Spec R)`.
   PASS: opened `fpqcPrecoverage`, `propQCPrecoverage`, `qcPrecoverage`,
   `QuasiCompactCover`, and `exists_isAffineOpen_of_isCompact`. The intersection
   imposes flatness of all arrows and finite quasi-compact-open coverage for each
   affine open. Finite affine covers of those compact opens give precisely 022B.
   Forgetting duplicate arrows in the presieve changes neither condition.
5. Finite set J: `∃ (n : ℕ)` with J represented by `Fin n`. PASS: every finite
   set can be enumerated in this way, and n=0 is allowed.
6. Indices a:J→I: `a : Fin n → I`. PASS: neither injectivity nor distinctness
   is required, as in the source.
7. Opens V_j⊆T_{a(j)}: `V : ∀ j, (T (a j)).Opens`. PASS: actual opens of
   the chosen original member, with canonical inclusion `(V j).ι`.
8. Affineness and V_j=Spec(A_j): `∀ j, IsAffineOpen (V j)`. PASS: read the
   definition `IsAffineOpen U := IsAffine U` and `Scheme.isoSpec`. Choose A_j as
   Γ((V j).toScheme,⊤); the affineness assertion supplies its canonical spectrum
   identification. Choosing these canonical coordinate rings is equivalent to the
   node's existential coordinate-ring presentations and omits no condition.
9. Induced R→A_j: `((ΓSpecIso R).inv ≫ ((V j).ι ≫ f (a j)).appTop).hom`.
   PASS: `ΓSpecIso R : Γ(Spec R,⊤) ≅ R`, so its inverse first maps R into
   base sections; `appTop` then pulls sections back to the chosen open subscheme.
10. Product map and faithful flatness: `RingHom.pi (fun j : Fin n ↦ ... )`
    followed by `.FaithfullyFlat`. PASS: the dependent product has exactly the
    coordinate rings above, with no unrelated map quantified. Read
    `RingHom.FaithfullyFlat` and `iff_flat_and_comap_surjective`; this is the
    dependency's faithful-flat ring-map notion. No separate coverage clause is
    demanded by the node's conclusion. Quantifiers occur after the family and
    covering hypothesis and before both conclusion clauses, as required.

Dependency review: `def-pc-scheme` records Mathlib `Scheme` and `Scheme.Hom`;
I read their locally-ringed-space signatures. `def-weil-pbc-fpqc-covering` records
`Scheme.fpqcPrecoverage`, whose signature and underlying conditions were checked
above. `def-weil-pbc-faithfully-flat-ring-map` records `RingHom.FaithfullyFlat`,
which assigns the target its algebra/module structure through the stated ring map.
All three notions are used directly; no private copy or extra instance appears.

Edge cases: empty I is allowed and can cover only an empty Spec(R). With zero R,
n=0 and the empty (zero) product give the allowed faithfully flat zero-ring map;
with nonzero R neither an empty fpqc family nor a faithfully flat empty product
is possible. Individual selected opens may be empty and original indices may
repeat. No field, characteristic, Noetherian, finite-presentation or individual
quasi-compact-source hypothesis is introduced. Universes u and v and all binders
are explicit; the theorem varies over every scheme/ring universe u and index
universe v, and has no quantification over undersized test objects.

Independent duplicate searches (using different query words from the worker):

- LeanFinder: "quasi compact flat covering family select finitely many affine
  open subschemes whose rings have faithfully flat product". Eight hits, including
  `QuasiCompactCover.exists_isAffineOpen_of_isCompact`; opened its signature:
  it gives affine opens and image equality for a quasi-compact hypercover, with
  no flat-arrow premise or faithfully flat ring-product conclusion. It is a
  useful proof ingredient, not an exact match.
- Loogle: `RingHom.pi, RingHom.FaithfullyFlat`: zero hits.
- LeanSearch: "finite collection of affine open subsets of flat covering with
  faithfully flat coordinate ring product": unavailable, Internal Server Error.
- `msearch.py grep`: `exists_isAffineOpen_of_isCompact|FaithfullyFlat.*pi|pi.*FaithfullyFlat`:
  ten hits; no complete matching statement.
- `rg` on Mathlib, WeilConjectures and project Lean for
  `exists_finite_affine_flat|affine.*[Rr]efin|standard.*[Cc]over|faithfully.*[Pp]roduct|fpqc.*[Aa]ffine`.
  Opened upstream `exists_finite_affine_flat_of_mem_fpqcTopology`: it selects
  arbitrary affine sources in a sieve, not opens of the given family, and has
  no product-ring assertion. Opened project `exists_fpqc_singleton_affine_refinement`:
  it concerns one morphism and a coproduct, not this family/product statement.
  The fppf refinement requires local finite presentation. No exact duplicate.

H5/H6/H8/H9: one theorem with `by sorry`, no definitions or proved auxiliary results;
source and blueprint marker on module and declaration; all three node proof steps
and their dependency names are in the docstring. Both imports supply used notions.
No unbound variable, namespace collision or overlength Lean line was found.
The recorded `lean.statement` is verbatim the theorem signature before `:=`.

Validation: server `scompile.py F1 lem-weil-pbc-fpqc-affine-standard-refinement
lean/Sheaf/AlgebraicGeometry/FpqcAffineStandardRefinement.lean` passed in 1.7 s,
exit code 0, without errors or warnings. Delivery preflight is run after this reading.
