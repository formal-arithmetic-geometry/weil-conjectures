## Worker report

Q144, stage 1, 2026-10-18. Repair of the return for head `60a5315a70`. I compared the retained sandbox with the current repository: the item remains imported with the same statement, and neither retained helper is on main. The required initial resumption dry run exited `OK (not pushed)` at `16127983ab`. That mechanical pass did not validate the returned mathematics; the proof has now changed substantively.

1. Files written (all node files are in `dag/nodes/sec-deligne-laumon-a1/`):

- `lem-per-artin-gabber-affine-curve.json`: repaired seven-step split; statement unchanged, statement dependencies completed.
- `lem-per-qbar-affine-support-bound.json`: retained helper, corrected to an arbitrary-field adic sheaf support estimate only; unsplit, no Mathlib match.
- `lem-per-qbar-fibre-compact-support-amplitude.json`: retained helper, corrected to arbitrary-field compact-support stalks and amplitude; unsplit, no Mathlib match.
- `lem-per-qbar-ordinary-adjunction.json`: new arbitrary-field ordinary adjunction on the actual adic categories; unsplit, no Mathlib match.
- `lem-per-qbar-arbitrary-field-duality.json`: new relative duality, biduality and direct-image exchange on arbitrary-field adic categories; unsplit, no Mathlib match.
- `lem-per-qbar-middle-tstructure.json`: new general-dimensional middle perverse t-structure and orthogonal characterization; unsplit, no Mathlib match.
- `citations.json`: 27 verbatim statement quotations covering every step citation. `fixes/repair.md`: point-by-point repairs. Previous item, report and certificate are preserved under `fixes/`. The previous search log is retained and extended.

2. Attachments: none. I searched the blueprint tag and perverse pushforward names in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and read `SixFunctors/Etale/Perverse/Operations.lean:199–223`. Both `AlgebraicGeometry.Etale.DerivedCategory.isPerverseLE_lowerShriek` and `AlgebraicGeometry.Etale.DerivedCategory.isPerverseGE_lowerShriek` still have `sorry`. They also concern ordinary finite-coefficient derived categories with a finite-Tor hypothesis, not the adic category here.

3. WANTED: none. I used the local BBD and Bhatt–Scholze PDFs, the main-20261015 blueprint proof, and Stacks `etale-cohomology.tex`, Tag 0F0X (`lemma-interlude-I`). No SGA source was used.

4. What changed: the unsupported compactification/boundary argument is replaced by BBD 4.2.4's pullback-dimension, adjunction and duality argument. The affine sheaf support estimate separately gives the stronger lower bound $Rf_!({}^pD^{\ge0})\subset{}^pD^{\ge0}$. Every helper has the actual coefficient and field domain. The false “equivalently” clause and ordinary-cohomology citation are removed.

5. Remaining work: all five helpers are intentionally statement-only unsplit nodes. No Lean was written, compiled or built; the upstream proofs remain sorry-backed. The item itself has a complete argument from its cited statements.

## Source error

The main-20261015 proof says that the sharper affine cohomological range applies to its compact-support fibre calculation. This is false: $H_c^2(\mathbf A^1,\overline{\mathbf Q}_\ell)=\overline{\mathbf Q}_\ell(-1)$ over an algebraically closed field. Its Step 2 uses curve generating blocks for schemes of arbitrary dimension without establishing the needed dimension trade. The returned boundary-induction replacement also fails as the maintainer explained. The repaired proof follows the named BBD source 4.2.4 instead. This corrects the imported proof, not the item statement or the unit's Fourier-exactness statement.

BBD 4.0 restricts fields for its older definition of the adic category. I did not apply that definition to arbitrary $k$. The new helpers use modern completed/common-stage categories, with the arbitrary-field operations and relative duality of Bhatt–Scholze §6.7, Proposition 6.8.14 and Remark 6.8.15. The t-structure helper states the BBD construction in these categories. Finite-type schemes over a field are excellent and finite-dimensional, and the prime is invertible; the relative dimension function is residue transcendence degree over $k$. These are the relevant geometric hypotheses of §6.7. There is no unsupported reduction from arbitrary $k$, or from $k_0$, to $\overline{\mathbf F}_q$.

## Not duplicates

`lem-per-qbar-affine-support-bound` vs `lem-kun-affine-direct-image-support-bound`: the latter is the Tag 0F0X result for torsion abelian etale sheaves; the helper is the closed-support inequality in the adic common-stage standard heart, requiring the nontrivial adic passage.

`lem-per-qbar-affine-support-bound` vs `lem-kun-affine-support-vanishing`: the latter gives torsion cohomology vanishing on transcendence-degree loci, not adic higher-direct-image support.

`lem-per-qbar-affine-support-bound` vs `lem-kun-0f10`: the latter gives finiteness of torsion cohomological dimension, not this adic sheaf inequality.

`lem-per-qbar-affine-support-bound` vs `lem-kun-strict-local-algebraic-residue-models`: the latter constructs strict-local geometric models, not a direct-image bound.

`lem-per-qbar-affine-support-bound` vs `lem-kun-transcendence-degree-tower`: the latter is a field-theoretic cardinal equality, not a sheaf theorem.

`lem-per-qbar-affine-support-bound` vs `lem-kun-coefficient-image-residue-algebraic`: the latter proves algebraicity of residue-field extensions in a coefficient-image affine construction; it has no higher direct-image or support-dimension assertion.

`lem-per-qbar-affine-support-bound` vs `lem-kun-strict-local-coefficient-chart`: the latter constructs a coefficient-compatible affine chart for a strict localization; it does not state an affine direct-image support bound.

`lem-per-qbar-affine-support-bound` vs `lem-kun-strict-local-coefficient-presentation`: the latter presents a strict localization as a filtered etale colimit with coefficient data; it does not concern $Rf_*$ or cohomology-sheaf supports.

`lem-per-qbar-affine-support-bound` vs `lem-kun-strict-local-rational-chart`: the latter constructs a rational chart and transcendence-degree equality in a strict-local ring; it gives no direct-image estimate.

`lem-per-qbar-affine-support-bound` vs `lem-per-artin-gabber-affine-curve`: the helper is an ordinary cohomology-sheaf estimate for $Rf_*$ without a relative-dimension parameter; the item concerns both shifted perverse classes for $Rf_!$. Steps 3–5 carry the main upper-bound argument, and Steps 6–7 carry the truncation and duality argument for the lower bound.

`lem-per-qbar-fibre-compact-support-amplitude` vs `lem-dg-compact-support-amplitude`: the latter is explicitly finite-ring ordinary-derived-category compact support; the helper adds adic coefficients and the geometric-stalk identification.

`lem-per-qbar-fibre-compact-support-amplitude` vs `fin4-lem-fibrewise-cohomological-dimension`: the latter bounds ordinary cohomology. It is no longer cited or among the helper's dependencies.

`lem-per-qbar-ordinary-adjunction` vs `fix-prop-adjunctions`: the latter assumes the fixed algebraic closure of a finite field; the helper allows arbitrary fields.

`lem-per-qbar-ordinary-adjunction` vs `det-thm-sf-ctf-stability-adjunctions`: the latter uses the lecture-notes condensed-module constructible finite-Tor setting, assumes positive characteristic through its setting, and supplies no identification with the actual raw rational/common-stage categories over arbitrary fields.

`lem-per-qbar-ordinary-adjunction` vs `def-sfb-module-derived-pushpull-adjunction`: the latter is an ambient derived adjunction for condensed-ring module objects, without this bounded-constructible restriction and adic transport.

`lem-per-qbar-ordinary-adjunction` vs `prop-weil-pbc-derived-inverse-image-adjunction`: the latter is for bounded-below ordinary abelian etale sheaves. The additional candidate `lem-a1-rational-direct-image-realization` identifies a rational direct-image realization, but does not state this adjunction or its common-stage form.

`lem-per-qbar-arbitrary-field-duality` vs `thm-sf-verdier-exchange`: the latter assumes $k=\overline{\mathbf F}_q$ and its coefficient datum; the new helper permits arbitrary $k$ and specifies relative duality and biduality as well as exchange.

`lem-per-qbar-arbitrary-field-duality` vs `thm-coef-qbar-verdier`: the latter again assumes the fixed finite-field datum.

`lem-per-qbar-arbitrary-field-duality` vs `prop-functor-package`: all seven clauses of that package retain the fixed algebraic closure of a finite field, so it cannot be applied here.

`lem-per-qbar-middle-tstructure` vs `thm-a1-curve-perverse-heart`: the latter requires a smooth pure-dimensional curve over a perfect field; it does not state the general-dimensional t-structure needed in adjunction.

`lem-per-qbar-middle-tstructure` vs `def-per-perverse-subcategories`: the latter only defines the classes and a heart candidate. It asserts neither the t-structure nor its orthogonal characterization.

## Searches

I searched the whole DAG, the blueprint with `tools/blueprint_refs.py search` (perverse, perverse t, t-structure, adjunction, pullback adjunction, duality and biduality), and the Lean source for the notions and proposed ids before creating nodes. I read the candidates above and their field conventions. Searching Tag 0F0X throughout the DAG yielded the six pairs above. No blueprint node states the additional helpers on their actual domains. Ancestry is the item's blueprint id, with empty `via` and no exact `same_as`.

Every helper has real `msearch.py` LeanFinder, LeanSearch, Loogle and grep records. Each of the three additional helpers has two semantic phrasings. The retained helpers keep their earlier records, honestly including malformed old Loogle patterns, and add a new phrasing and valid Loogle queries. All services answered. The hits concern standard derived t-structures, ordinary module-sheaf adjunctions, Verdier localization, affine inverse limits or finite-dimensional vector-space duality. None states the helper.

I read Mathlib `CategoryTheory/Functor/Derived/Adjunction.lean:144`, `CategoryTheory.Adjunction.derived`: it needs specified derived functors and composite-derived-functor hypotheses. Establishing constructibility, completed pullback, rational transport and common-stage geometric functors here is not a one-line specialization. `DerivedCategory.TStructure.t` is the standard derived t-structure, not middle perversity. No Mathlib leaf is claimed.

## Review by Q144

I read BBD 1.3.17(iii), 2.2.11–2.2.19, 4.0, 4.1.1–4.1.2, 4.2.3–4.2.4, the main-20261015 blueprint proof, and BS 6.7.1–6.7.2, 6.7.5–6.7.7, 6.7.10, 6.7.13–6.7.14, 6.7.18–6.7.21 and 6.8.14–6.8.15. I opened every cited node statement. The item remains the source's fibre-dimension upper bound and a weaker form of its affine lower bound, with no altered hypotheses or conclusions.

For each helper I checked its actual source: the affine helper is BBD 4.1.1's sheaf inequality, with the finite-level Tag 0F0X calculation. It has no proof sketch, dimension parameter, equivalence or perverse-complex conclusion. The fibre helper uses BS 6.7.10 and the finite compact-support bound, not ordinary $H^q$. The ordinary adjunction is precisely BS 6.7.2 and the field/common-stage passage of 6.8.14–6.8.15. The duality helper uses the constructible exceptional adjoint of 6.7.19, biduality of 6.7.20, and the exchange from the internal-Hom/projection formalism in 6.7.13–6.7.14, with relative normalization fixed explicitly. It does not assert an unrestricted unbounded ambient exceptional adjoint. The middle helper is BBD's general-dimensional construction in these modern categories, with the exact shift, extension and orthogonal clauses needed below. These are structural inputs, not renamed affine-pushforward clauses.

Step 1: `lem-dg-compact-support-amplitude` literally states $R^qf_!F=0$ for $q>2d$. I checked separated finite type, a finite coefficient ring and invertible exponent. The corrected adic helper supplies its own stalk formula and range. This is only the preliminary range; no perverse upper bound is inferred from $2d$.

Step 2: all three structural helpers refer to arbitrary $k$ and the actual adic category. Duality supplies both exchange and biduality; the t-structure theorem is cited in addition to the class definitions. Interchange of shifted classes follows from the cosupport definition and $D^2=1$. Neither `thm-sf-verdier-exchange` nor `def-trf-dualizing-complex` is used outside its finite-field/finite-coefficient scope.

Step 3: `lem-per-adic-heart-pullback-fibres` permits arbitrary morphisms here and states standard cohomology exactness and the fibre identity. This gives inclusion of the closed cohomology support in the closed inverse image. The second clause of `lem-zl-finite-type-fibre-image-dimension-bounds` is applied to $X\times_Y Z\to Z$, with $Z$ the reduced closed support, $\dim Z\le i$. Both schemes are finite type over $k$. `lem-sc-fibre-dimension-after-base-change` supplies the local dimension equality converting the geometric-fibre hypothesis to the scheme-fibre hypothesis in the dimension inequality. No smoothness, flatness, properness, dominance or pure-dimensionality is used. Empty support and $i<0$ are removed before applying a lemma with nonnegative bounds. The result is $\dim\operatorname{Supp}\mathcal H^{-i}(Lf^*A)\le i+d$, hence $Lf^*A\in{}^pD^{\le d}$, equivalently $Lf^*A[d]\in{}^pD^{\le0}$.

Step 4: the ordinary adjunction gives exactly the Hom bijection used. The middle-t-structure helper gives orthogonal recognition. Testing against every $A\in{}^pD^{\le-d-1}(Y)$, whose pullback lies in ${}^pD^{\le-1}(X)$, gives $Rf_*B\in{}^pD^{\ge-d}(Y)$. This is the correct sign in BBD 1.3.17(iii); no t-structure theorem is inferred from a definition.

Step 5: exchange has type $D_YRf_!K\cong Rf_*D_XK$ on bounded constructible field-coefficient objects. Apply Step 4 to $D_XK$, then biduality and the class interchange of Step 2. This proves the required ${}^pD^{\le d}$ upper inclusion and replaces the invalid boundary induction in full.

Step 6: the affine helper applies to $F_i=\mathcal H^{-i}K$ with support bound $i$; nonzero $F_i$ has $i\ge0$. Its bound $i-q$ is $-j$ in degree $j=q-i$ of $Rf_*F_i[i]$. `lem-per-adic-heart-pullback-fibres` supplies the bounded standard t-structure; clause 1 of `lem-weil-heart-short-exact-triangles` states its truncation triangles. The ordinary-adjunction helper supplies exactness of $Rf_*$ and the middle helper supplies extension closure. The finite truncation argument therefore proves the full affine ordinary-direct-image bound. No adic sheaf is substituted into a torsion statement.

Step 7: apply the same arbitrary-field exchange to $K\in{}^pD^{\ge0}$. Step 6 and the support/cosupport definitions give the stronger compact-support bound ${}^pD^{\ge0}$; shifted t-structure nesting weakens it to ${}^pD^{\ge-d}$ for $d\ge0$. Empty source and the relative-dimension-one projection are explicitly covered.

Small cases checked: empty schemes, zero sheaves, identity and finite morphisms ($d=0$), skyscraper sheaves ($a=0$), and $\mathbf G_m\hookrightarrow\mathbf A^1$ (the ordinary $R^1j_*$ is boundary-supported, as required). For $\mathbf A^1\to\operatorname{Spec}k$, $K=\overline{\mathbf Q}_\ell[1]$ has compact-support output $\overline{\mathbf Q}_\ell(-1)[-1]$, in perverse degree 1; the upper bound must allow $d=1$. For $\mathbf A^1\times\mathbf A^1\to\mathbf A^1$, $K=\overline{\mathbf Q}_\ell[2]$ gives the constant sheaf with twist in ordinary degree zero, hence perverse degree 1. Both satisfy the repaired bounds. Shifts give the stated indices. At a point, middle perversity is the standard t-structure and relative duality is coefficient-vector-space duality. These examples test the old ordinary/compact-support confusion and the adjunction signs.

For B1–B7, each new node is self-contained, statement-only with empty proof lists, has defined objects and coefficient domains, cites its notions and uses delimited TeX. C1/C4 are checked above and certified by verbatim quotes. The four off-unit tools are declared only in `split_report.tool_uses`, with reasons; no maintainer acceptance or top-level `tool_uses` is invented. Every proof step is under 1,100 characters, so none is a long step hiding another lemma. The rejected proof is retained under `fixes/`, and `fixes/repair.md` answers each return point.

## Validation

The server check_dag reported no introduced finding; review_split reported PASS. The substantive repaired split passed deliver.py --no-push at 5ac27c0d02. Two inherited grep-query records were then normalized to the exact query strings in searches.jsonl, moving the directory information to results. The required final dry run is repeated for that metadata correction before pushing.
