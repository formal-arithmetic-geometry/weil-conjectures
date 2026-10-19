# nt-target-smooth-purity-qbar

## Worker report

1. Files written: `dag/nodes/sec-smooth-purity/nt-target-smooth-purity-qbar.json` (six-step split); `lem-pur-finite-smooth-adjunction-general-base.json` (statement-only finite trace and derived-reduction input); `lem-pur-condensed-exceptional-reconstruction.json` (statement-only conditional comparison with the specified condensed adjoint). Both new nodes remain unsplit; there are zero Mathlib leaves. `citations.json` contains every step/citation pair with a verbatim statement. Sandbox-only source reading aids, original report, search outputs and hashes are in `source-evidence/`; complete exact-source texts are also embedded below so the committed report supplies them locally to the next reader.
2. Attachments: none. Read-only searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item tag, full target name, `smoothPurityIso`, `tateTwistDerived` and condensed coefficients found no complete attachment. `AlgebraicGeometry.Etale.smoothPurityIso`, Smooth/Basic.lean:310, takes orientation and tensor comparison arguments and has ordinary etale coefficients. `nonempty_iso_rightDerivedUpperShriek_twistShift` in that file proves an ordinary etale finite-coefficient conclusion under its normalized-twist instance, not the finite node's full coefficient-reduction/cocycle assertion and not condensed Qbar purity. Master `smoothPurityIso` at line 88 has body `sorry` and is specification only.
3. WANTED: no source remains missing for the returned endpoint checks. The exact commit and relevant imports were recovered by a read-only export from the server's `/home/ubuntu/sidebuild-base/repo.git`. Nothing was fetched into or written in the live project, the shared repository, its literature directory, or the launcher. The shared local literature cache still lacks these master files; the complete source exhibits below remove any need for the next reviewer to access that cache or SSH. No new paper was downloaded. The SGA and Bhatt–Scholze PDFs were read in the existing `/home/ubuntu/weil-launcher-nt/literature/` cache.
4. What was wrong: the preceding report certified exact-source agreement while using an unavailable target archive and a different-revision Tate reference. Those earlier PASS assertions are withdrawn and replaced by the reading below. The seed's direct substitution into the finite-field common-stage purity theorem also required correction, as described under STATEMENT-DISPUTED. The new exceptional comparison's source has been changed to name the exact master construction and explicitly identify the comparison as an agent-formulated obligation, not a theorem of Bhatt–Scholze.
5. Remaining work: the two new nodes deliberately have no proofs and join stage 1's queue. This delivery proves the parent conditional on their stated conclusions, as a one-level split requires. It neither claims the whole target closure is proved nor treats master sorry declarations as completed proofs. No Lean was authored or edited, no compiler/Lake/build ran, and no push was made. A fresh second reader must review and deliver after the required dry run.

## STATEMENT-DISPUTED: explanatory identification

The seed described the map as a direct specialization of `thm-pur-rational-and-qbar-purity`. That node fixes the global finite-field datum, whereas the source permits every positive-characteristic field with ell invertible. The concrete example k = F_p(t) meets the target assumptions and cannot be substituted into that theorem. Its common-stage Qbar category also differs from the source's condensed module-object category. The corrected explanation retains every target hypothesis and both endpoints: use finite purity over the actual field, reconstruct a coherent integral tower, then compare coefficient realizations and the chosen adjunction. No geometric condition is added; no conclusion or case is dropped. The upstream module docstring says normalization and additional composition/base-change equations are intended but not stated in this chosen-isomorphism signature. The construction follows the SGA normalization without adding those equations to the target.

## Repair of the re-issued L return: F1/F2/C4

The full independent return `NC__nt-target-smooth-purity-qbar__c90497ea5ead/review.md` was read. Its issue is unavailable exact sources, not a mathematical counterexample or a request to compile. This repair addresses each concrete request:

1. **Exact master target and imports, F1.** Found commit `7347520d9b0d17cc31d0fc34ea20f1381a83fe13` in an existing source object store. Exported immutable blobs using read-only `git show <commit>:<path>` on that server store; no git command ran in the shared repository. Each complete source is reproduced below with Git blob and SHA-256 hashes, both recomputed from the copied bytes in the sandbox. The server's existing `literature/upstream-master-20261016/.../SmoothPurity/Defs.lean` has the same SHA-256 as the commit's target blob. Thus the signature and imports here are exactly the target revision, not the old October 14 checkout or the previously used sidebuild revision.
2. **The exceptional comparison, F2/C4, Step 4.** Exact `UpperShriek.lean` lines 100–118 and 128–146 define the right adjoint as a chosen proper-pushforward right adjoint followed by open pullback, with the composite adjunction. Exact `BoundedConstructible.lean` lines 254–315 chooses the compactification and defines compact-support image as open extension followed by proper direct image. The new comparison lemma now spells out this same order and adjunction. Its source explicitly says the reconstruction/counit comparison is an additional agent-formulated unsplit obligation. Read Bhatt–Scholze Proposition 6.8.14 and Remark 6.8.15, printed pp. 61–62: the former gives coefficient-category equivalences and the latter discusses six functors under its finiteness assumptions. Neither establishes this particular condensed right-adjoint comparison. Step 4 cites the new lemma's actual conclusion, not the paper for that missing theorem. There is no assertion of an unbounded ambient pro-etale adjoint.
3. **The Tate endpoint, F2/C4, Step 5.** Exact `TateTwist/ProEtale.lean` lines 119–144 defines the finite levels as `Mod.freeFunctor` on the abelian roots-of-unity sheaf, with ell-th-power transitions and the inverse limit indexed by natural numbers including zero. The imported `ModuleObjects/Free.lean` defines that functor as R tensor M in the category of abelian sheaves, so it is not the free module on the underlying set. The root sheaf and power maps are the sheafifications explicitly defined in the exact `RootsOfUnity.lean`. At positive levels, the step's coefficient-ring calculation identifies these modules with mu_(ell^n), compatibly with the power maps; at zero the sheaf mu_1 is zero, and deleting it does not change the limit by the written cone argument. Lines 81–103 and 150–154 extend along the inclusion through the bottom finite intermediate field, exactly the composite Z_l to Q_l to Omega used by U. Lines 158–179 give zeroth tensor power equal to the unit, positive tensor powers, and degree-zero derived inclusion. Step 5 now explicitly names that coefficient map and writes the balanced scalar-extension and tensor maps, so the identification uses these exact definitions rather than a different-revision docstring.
4. **Signature and orientation, Step 6.** Exact `SmoothPurity/Defs.lean` lines 76–92 quantify ell prime, field k of prime positive ring characteristic unequal to ell, X and Y over Spec k with locally finite type, quasi-compact and separated structure maps, f over k, and natural d with `SmoothOfRelativeDimension d f.left`. Its left endpoint is the ambient object underlying the chosen exceptional image of the constructible tensor unit; its right endpoint is `shiftFunctor (2*d : Z)` on `tateTwistDerived X.left ell d`. Inverting Step 4's map and using Step 5 gives exactly that type. The full-subcategory inclusion changes neither the morphism direction nor the shift. The signature asks for isomorphism data with no further coherence fields. The target's own sorry and its framework's sorried instances are not used as proofs.

## Review by NC

This is the repair worker's own source reading, not a claim of an independent second reading. I read AGENTS.md, the stage-1 brief and stage document, SETUP.md's three levels, GOAL.md, dag-sync.md, delivery-errors B–E in full, the returned review, the chapter and `sk-thm-purity-transport` records, and the complete statements of all cited nodes. The chapter remains fixed. The proof realizes the unit's Steps 1–3: finite reductions, integral reconstruction, rationalization/finite-field scalar extension. Its structure-morphism Step 4 does not replace general f. This target is not the unit's key node, so no realization record was edited.

**Step 1.** `lem-pur-finite-smooth-adjunction-general-base` supplies gamma_(n,K), compatibility with derived quotient reduction, the quotient cocycle, and for K = A_n the single degree -2d. I read SGA 4 XVIII 3.2.5 (printed pp. 585–586), the trace formulation 2.13.2, and 3.1.12.1. Smooth compactifiable f and an invertible annihilator are their hypotheses; no algebraically closed finite-field base is required. The lemma includes the finite etale/pro-etale transport and derived-reduction compatibility as obligations for its future split. SGA 3.1.12.1 itself is only restriction of scalars, and is not misquoted for the derived-reduction square. Ell is invertible in the given field, and K = A_n has Tor amplitude [0,0]. The explicit twist tower and a second identical copy equipped with the gamma_n level identifications give a strict model; no lifting of an arbitrary derived diagram is assumed.

**Step 2.** Opened all seven cited statements. `lem-weil-pbc-normalized-constructible-local-effectivity` requires a strict normalized tower with quotient cocycle, constructible finite-level cohomology and uniform bounds; Step 1 supplies these. `lem-weil-pbc-reconstruction-uniform-tower` then gives the reconstructed object's local models, completeness and compatible reductions. `def-weil-pbc-bounded-constructible-complete` additionally requires compatible etale-origin witnesses, supplied by the actual roots-of-unity sheaves and their tensor powers. The explicit global rank-one model of the unit tower gives L equal to the integral coefficient object. `pqf-lem-locnoeth-lft`, `lem-weil-pbc-qcqs-over-affine` and `lem-kun-dimension-finite-type` give the Noetherian, qcqs and finite-dimensional prerequisites over a field; a field is Noetherian since its ideals are 0 and itself. The bounds are [-2d,-2d] on X and [0,0] for the unit on Y. This uses the cited reconstruction statements, not the weaker constant-coefficient Stacks definition as a comparison theorem.

**Step 3.** `lem-weil-tower-category-levelwise-abelian` states that evaluation is exact and kernels/cokernels are levelwise; `lem-weil-pbc-ringed-strict-tower-homotopy-limit` supplies an exact Rlim functor on strict tower complexes. The chosen comparison is already an identity between two copies of the strict complex. Its cone is levelwise acyclic, and applying a functor to the isomorphism and inverse preserves them. This is elementary given the cited statements; no exactness of ordinary infinite products is used.

**Step 4.** Opened the full conditional `lem-pur-condensed-exceptional-reconstruction` statement. It requires exactly the normalized effective exceptional tower and its integral membership established in Steps 1–2. It states the isomorphism to the specified constructible right adjoint, the counit comparison and the unit/shift clauses used here. I matched its functor and adjunction to exact-master UpperShriek and BoundedConstructible definitions, as detailed in the return repair. I changed the lemma's source attribution and Step 4's source so neither suggests that Bhatt–Scholze supplies that comparison. This is a substantive unsplit input, without smoothness or Tate purity in its conclusion.

**Step 5.** Opened all six cited statements. `lem-weil-pbc-condensed-point-basis-evaluation` computes p_X^*F on affine weakly contractible objects; `lem-weil-pbc-proetale-affine-wcontractible-covering-family` supplies coverings by them. The written continuous-function calculation proves the integral ring comparison and its ell^n quotient on that basis, so inverse-image preservation of an infinite limit is not assumed. `lem-pur-twist-sheaf-locally-free` supplies the locally free complete Tate line and its reductions for any scheme with ell invertible. Locally choosing its rank-one generator proves the statements for its d-fold power and shows there is no higher Tor. `lem-weil-pbc-reconstruction-uniform-tower` applies to the explicit global line model, whose reduction tower is the actual P tower; its identity-cover model supplies the global comparison. `lem-weil-pbc-condensed-e-realization` and `prop-weil-pbc-qbar-condensed-two-colimit` state the derived scalar extensions and tensor transitivity used. I matched them to exact-master coefficient definitions, and checked every Tate constructor, map, and indexing choice. The balanced maps written in the repaired step give the ordinary tensor comparison; on locally free lines ordinary tensors compute the derived ones. The exact code's d=0 constructor and degree-zero singleFunctor give the unit and derived endpoint.

**Step 6.** Uses only inversion, composition and inclusion of a full subcategory after Steps 4–5. Read the exact target signature and section variables; the resulting arrow has the specified left object and positive twist d and shift 2d. It introduces no properness, algebraic closure, or ambient exceptional-adjoint hypothesis. A statement of additional base-change/trace equations is not silently added.

**Each new node, B1–B7, C1/C4, D1/D2.** Both new nodes introduce their fields, schemes, rings, coefficient categories, functors and hypotheses. Both have empty proofs, empty proof dependencies and null proof origins: they are statement-only frontier obligations. The finite input is earlier torsion geometry with a normalized coefficient-change square; the reconstruction input is a generic conditional exceptional-adjoint comparison with no smoothness, dimension or Tate conclusion. Neither merely restates the parent's condensed smooth-purity clause. The finite input follows the SGA source above with its extra coherence obligation identified. The second is now honestly sourced as an agent-formulated comparison to the exact chosen master adjunction, motivated but not asserted by Bhatt–Scholze. An arbitrary noneffective family of finite objects is never claimed effective: the comparison explicitly assumes a strict normalized bounded tower and an integral reconstruction with canonical reductions. The source references have exact places, all non-elementary facts used in the parent have cited statements, and all 17 citation occurrences have verbatim evidence below and in citations.json.

**Search and small cases.** Ran full-DAG key-word/source searches and whole-blueprint searches for smooth purity, exceptional reconstruction, condensed coefficients, coefficient reduction and Tate twists, and reopened the near matches listed under Not duplicates. The computed blueprint ancestor is null because the maintainer-seeded node's created.item is a batch description; preserved that computed metadata and the seed's explicit blueprint route, without editing maintainer ancestry. Repeated all Mathlib searches through msearch.py for the item and each new node, with two semantic phrasings, Loogle and grep; the 15 actual queries/digests are in searches.jsonl and the node fields. All services worked in this run. Read the returned signatures: general equivalences/adjoint uniqueness, ordinary structure-sheaf adjunctions, algebraic etaleness/traces, and discrete/solid condensed constructions do not give these geometric statements. No stale unavailable/no-match records are carried forward. Checked d=0 and identity f (unit, no shift, etale adjunction), d=1 for A1 over k (one Tate line in degree -2), n=1, K=0/L=0, empty source, and k=F_p(t). The finite new node also allows characteristic zero as SGA does; the target and condensed comparison retain positive prime characteristic. A non-proper smooth A1 projection is allowed. The sole-degree assertion permits the zero object; it does not demand a nonzero cohomology sheaf on the empty scheme. These checks found no new statement dispute.

**What changed for this return.** Replaced the different-revision source reference by exact immutable source objects and complete local report exhibits; corrected the exceptional-comparison attribution; specified the actual chosen adjunction in the comparison node and Step 4; expanded the bottom-field scalar-extension and tensor maps and cited exact Tate constructors in Step 5; bound Step 6 to the exact target signature; reran and replaced search evidence and regenerated citations. Earlier reader reports are retained only as sandbox historical reading material, not represented as a fresh second reading. No framework source was modified or compiled.

## Not duplicates

lem-pur-finite-smooth-adjunction-general-base vs thm-pur-finite-coefficient-smooth-purity: the existing node fixes the global finite-field datum; the new finite input works over arbitrary k with ell invertible and includes the explicit derived quotient compatibility.
lem-pur-finite-smooth-adjunction-general-base vs thm-pur-finite-reduction-of-purity: the existing reduction theorem likewise fixes the finite-field datum, which cannot cover k=F_p(t).
lem-pur-finite-smooth-adjunction-general-base vs lem-pur-finite-universal-smooth-trace: this existing finite-free coefficient-extension trace equality fixes the global finite-field datum and compares Z/ell^r to O_E/ell^r; it does not give arbitrary-ground-field purity and derived quotient reduction.
lem-pur-finite-smooth-adjunction-general-base vs thm-asd-smooth-tensor: the existing ordinary etale theorem leaves the rank-one orientation unidentified and does not supply the normalized Tate orientation or coefficient-reduction/cocycle assertion.
lem-pur-finite-smooth-adjunction-general-base vs cor-amb-affine-space-adjunction: the existing assertion is for affine-space projections, not every smooth morphism, and does not state coefficient-reduction coherence.
lem-pur-finite-smooth-adjunction-general-base vs lem-coef-finite-exceptional: the existing coefficient-change theorem fixes the global finite-field datum and does not give the smooth Tate orientation.
lem-pur-condensed-exceptional-reconstruction vs lem-weil-pbc-condensed-e-realization: the existing equivalence compares pullback and direct image and their adjunction, not the specified compact-support right adjoint and its exceptional counit.
lem-pur-condensed-exceptional-reconstruction vs prop-weil-pbc-qbar-condensed-two-colimit: the existing node supplies coefficient extension and a two-colimit category; it has no exceptional-adjoint comparison.
lem-pur-condensed-exceptional-reconstruction vs def-weil-exceptional-inverse-image: the existing definition uses completed/common-stage constructions rather than proving their comparison with the specified condensed chosen adjoint.
lem-pur-condensed-exceptional-reconstruction vs nt-target-smooth-purity-qbar: the new node has no smoothness assumption or Tate-purity conclusion; it supplies the separate reconstruction-to-adjoint interface used after the finite calculation.

## Validation

No compilation is authorized for this stage. The required `deliver.py NC nt-target-smooth-purity-qbar --no-push` performs DAG-only preflight in its own temporary worktree. Its output is saved in sandbox `repair-dry-run.log`; the worker returns READY only after it prints OK. All edits and source reading aids are confined to this sandbox. No source exhibits are added as Lean files to the delivery: the report alone carries the exact texts needed by the next reader.

## Verbatim citation evidence

Step 1, `lem-pur-finite-smooth-adjunction-general-base`:

```text
Let $\ell$ be prime, let $k$ be any field of characteristic different from $\ell$, and let $f:X\to Y$ be a $k$-morphism between separated finite-type $k$-schemes [def-weil-pbc-scheme-conventions], smooth of pure relative dimension $d\in\mathbf Z_{\geq0}$ [def-sbc-smooth-morphisms]. For $n\geq1$ set $A_n=\mathbf Z/\ell^n\mathbf Z$, and for $T=X,Y$ write $A_{n,T}$ for its constant sheaf on $T$. On each small pro-etale site [def-weil-pbc-proetale-site], let $D^b_{ctf}(T,A_n)$ consist of complexes with bounded constructible cohomology in the intrinsic finite-stratification sense of [def-weil-proetale-constructible-sheaf] and finite Tor amplitude: there are integers $a\leq b$ such that tensoring with any sheaf of $A_n$-modules in degree zero has cohomology only in $[a,b]$ [def-weil-proetale-tor-amplitude]. Let $Rf_{!,n}$ be compact-support direct image, formed by proper direct image after extension by zero in a compactification [def-compact-support-direct-image-detailed], and let $Rf_n^!$ be its constructible exceptional inverse image, obtained from the ordinary etale right adjoint by the etale/pro-etale comparison [def-weil-exceptional-inverse-image]. Write $A_{n,T}(1)=\mu_{\ell^n,T}$, the sheaf of $\ell^n$-th roots of unity, $A_{n,T}(d)=\mu_{\ell^n,T}^{\otimes_{A_n}d}$ with zeroth power $A_{n,T}$, and $K(d)=K\otimes^L_{A_n} A_{n,T}(d)$ [def-pur-roots-of-unity-sheaf, def-coefficient-twists-detailed].

The SGA-normalized smooth trace $Rf_{!,n}(Lf^*K(d)[2d])\to K$ has adjoint an isomorphism
$$\gamma_{n,K}:Lf^*K(d)[2d]\xrightarrow{\sim}Rf_n^!K$$
for every $K\in D^b_{ctf}(Y,A_n)$. Here the normalization is the trace of SGA 4 XVIII 2.9, 2.13.2 and 3.2.5; at relative dimension zero it is the etale adjunction. For every $n\geq1$ and $K\in D^b_{ctf}(Y,A_{n+1})$, the comparisons are compatible with the quotient map $A_{n+1}\to A_n$: derived reduction of $\gamma_{n+1,K}$ is $\gamma_{n,K\otimes^L_{A_{n+1}}A_n}$ under the pullback, twist and exceptional-image coefficient comparisons. Reduction from $A_r$ to $A_n$ agrees with successive reduction through $A_m$ for all $r\geq m\geq n\geq1$ under tensor associativity (the quotient cocycle).

For $K=A_{n,Y}$ the source and target of $\gamma_{n,K}$ have constructible cohomology only in degree $-2d$; their reductions, identified by these comparisons, satisfy the quotient cocycle.
```

Step 1, `lem-pur-twist-sheaf-locally-free`:

```text
Fix a prime $\ell$, a finite extension $E/\Ql$ with valuation ring $\mathcal O_E$,
uniformizer $\varpi_E$ and residue rings $A_{E,n}=\mathcal O_E/\varpi_E^n$,
$n\geq1$ [def-weil-finite-field-fiber], and a scheme $S$ on which $\ell$ is
invertible. On the small pro-etale site [def-weil-pbc-proetale-site] of $S$,
let $\mu_{\ell^r,S}$ be the sheaf of $\ell^r$-th roots of unity with transition
maps $u\mapsto u^\ell$ [def-pur-roots-of-unity-sheaf], let $\varprojlim$ be
the inverse limit of sheaves [def-pur-sheaf-inverse-limit] and $\otimes$ the
tensor product of sheaves of modules [def-pur-sheaf-tensor-product], let
$\widehat{\Zl}_S=\varprojlim_r(\mathbf Z/\ell^r\mathbf Z)_S$ and
$\widehat{\mathcal O}_{E,S}=\varprojlim_n(A_{E,n})_S$ be the completed
coefficient sheaves [def-weil-completed-integral-coefficients], and put

$$
 \Zl(1)_S=\varprojlim_{r\geq1}\mu_{\ell^r,S},\qquad
 \mathcal O_E(1)_S=\Zl(1)_S\otimes_{(\Zl)_S}(\mathcal O_E)_S,\qquad
 A_{E,n}(1)_S=\mathcal O_E(1)_S\otimes_{(\mathcal O_E)_S}(A_{E,n})_S .
$$

Then:

1. For every $r\geq1$ there is an etale covering $\{U_i\to S\}$ such that
$\mu_{\ell^r,S}|_{U_i}\cong(\mathbf Z/\ell^r\mathbf Z)_{U_i}$ as sheaves of
$(\mathbf Z/\ell^r\mathbf Z)_{U_i}$-modules; so $\mu_{\ell^r,S}$ is a locally
constant sheaf with finite stalks, locally free of rank one over
$(\mathbf Z/\ell^r\mathbf Z)_S$, and the transition maps
$\mu_{\ell^{r+1},S}\to\mu_{\ell^r,S}$ are surjective.

2. $\Zl(1)_S$ is a sheaf of $\widehat{\Zl}_S$-modules, and there is a pro-etale
covering $\{V_j\to S\}$ with $\Zl(1)_S|_{V_j}\cong\widehat{\Zl}_{V_j}$; so
$\Zl(1)_S$ is locally free of rank one over $\widehat{\Zl}_S$, and
$\Zl(1)_S\otimes_{\widehat{\Zl}_S}(\mathbf Z/\ell^r\mathbf Z)_S\cong\mu_{\ell^r,S}$
for every $r$.

3. $\mathcal O_E$ being a free $\Zl$-module of finite rank,
$\widehat{\Zl}_S\otimes_{(\Zl)_S}(\mathcal O_E)_S\cong\widehat{\mathcal O}_{E,S}$,
and $\mathcal O_E(1)_S$ is a locally free $\widehat{\mathcal O}_{E,S}$-module of
rank one with
$\mathcal O_E(1)_S\otimes_{\widehat{\mathcal O}_{E,S}}(A_{E,n})_S\cong A_{E,n}(1)_S$,
a locally free $(A_{E,n})_S$-module of rank one, locally constant with finite
stalks, for every $n\geq1$.

4. With the integral derived reduction over the completed coefficient sheaf
[def-weil-integral-derived-reduction],
$\mathcal O_E(1)_S\otimes^L_{\mathcal O_E}A_{E,n}\cong A_{E,n}(1)_S$ placed in
degree $0$ for every $n\geq1$; $A_{E,n}(1)_S$ lies in $D^b_c(S,A_{E,n})$
[def-weil-finite-torsion-constructibility] with cohomological support [def-weil-cohomological-support] contained in
$\{0\}$ (equal to $\{0\}$ when $S$ is nonempty);
$\mathcal O_E(1)_S$ is derived complete [def-weil-derived-complete]; hence
$\mathcal O_E(1)_S$ lies in the derived-complete integral category
$D^b_c(S,\mathcal O_E)$ [def-weil-derived-complete-integral-detailed].
```

Step 2, `lem-pur-finite-smooth-adjunction-general-base`:

```text
Let $\ell$ be prime, let $k$ be any field of characteristic different from $\ell$, and let $f:X\to Y$ be a $k$-morphism between separated finite-type $k$-schemes [def-weil-pbc-scheme-conventions], smooth of pure relative dimension $d\in\mathbf Z_{\geq0}$ [def-sbc-smooth-morphisms]. For $n\geq1$ set $A_n=\mathbf Z/\ell^n\mathbf Z$, and for $T=X,Y$ write $A_{n,T}$ for its constant sheaf on $T$. On each small pro-etale site [def-weil-pbc-proetale-site], let $D^b_{ctf}(T,A_n)$ consist of complexes with bounded constructible cohomology in the intrinsic finite-stratification sense of [def-weil-proetale-constructible-sheaf] and finite Tor amplitude: there are integers $a\leq b$ such that tensoring with any sheaf of $A_n$-modules in degree zero has cohomology only in $[a,b]$ [def-weil-proetale-tor-amplitude]. Let $Rf_{!,n}$ be compact-support direct image, formed by proper direct image after extension by zero in a compactification [def-compact-support-direct-image-detailed], and let $Rf_n^!$ be its constructible exceptional inverse image, obtained from the ordinary etale right adjoint by the etale/pro-etale comparison [def-weil-exceptional-inverse-image]. Write $A_{n,T}(1)=\mu_{\ell^n,T}$, the sheaf of $\ell^n$-th roots of unity, $A_{n,T}(d)=\mu_{\ell^n,T}^{\otimes_{A_n}d}$ with zeroth power $A_{n,T}$, and $K(d)=K\otimes^L_{A_n} A_{n,T}(d)$ [def-pur-roots-of-unity-sheaf, def-coefficient-twists-detailed].

The SGA-normalized smooth trace $Rf_{!,n}(Lf^*K(d)[2d])\to K$ has adjoint an isomorphism
$$\gamma_{n,K}:Lf^*K(d)[2d]\xrightarrow{\sim}Rf_n^!K$$
for every $K\in D^b_{ctf}(Y,A_n)$. Here the normalization is the trace of SGA 4 XVIII 2.9, 2.13.2 and 3.2.5; at relative dimension zero it is the etale adjunction. For every $n\geq1$ and $K\in D^b_{ctf}(Y,A_{n+1})$, the comparisons are compatible with the quotient map $A_{n+1}\to A_n$: derived reduction of $\gamma_{n+1,K}$ is $\gamma_{n,K\otimes^L_{A_{n+1}}A_n}$ under the pullback, twist and exceptional-image coefficient comparisons. Reduction from $A_r$ to $A_n$ agrees with successive reduction through $A_m$ for all $r\geq m\geq n\geq1$ under tensor associativity (the quotient cocycle).

For $K=A_{n,Y}$ the source and target of $\gamma_{n,K}$ have constructible cohomology only in degree $-2d$; their reductions, identified by these comparisons, satisfy the quotient cocycle.
```

Step 2, `lem-weil-pbc-normalized-constructible-local-effectivity`:

```text
Let $T$ be a Noetherian scheme and let $(A,I)$ be an adic coefficient datum [def-weil-pbc-adic-coefficient-datum], with $R_n=(A/I^n)_T$ and $A_T=\varprojlim R_n$ on $T_{\mathrm{proet}}$. Let $M_\bullet\in D(\operatorname{Tow}_A(T))$ be supplied with level objects $M_n\in D(\operatorname{Mod}(R_n))$ identifying their restrictions of scalars with its evaluations. Suppose there are normalization isomorphisms $M_{n+1}\otimes^L_{R_{n+1}}R_n\cong M_n$ whose scalar-extension maps induce its transitions and which satisfy the quotient cocycle. Assume each cohomology sheaf of each $M_n$ is constructible in the intrinsic finite-stratification, finite-lisse sense of [def-weil-proetale-constructible-sheaf], and that there are integers $a\leq b$, independent of $n$, with $\mathcal H^q(M_n)=0$ for $q\notin[a,b]$. Then each $M_n$ has bounded constructible etale origin in the sense of [def-weil-pbc-proetale-modules], and $M_\bullet$ admits the common finite stratification, pro-etale coverings, bounded adic-lisse finite-type local complexes, and normalization-compatible reduction isomorphisms required by [def-weil-pbc-bounded-constructible-tower]; in particular it is uniformly bounded constructible in that full sense. The local terms are not asserted to be projective. This assertion requires both the normalized derived reductions and the common cohomological interval, not merely levelwise constructibility.
```

Step 2, `lem-weil-pbc-reconstruction-uniform-tower`:

```text
Let $k$ be a field and let $T$ be a scheme of finite type over $\operatorname{Spec}k$ [def-weil-finite-type-morphism]. Let $M_\bullet$ be a uniformly bounded constructible adic tower in the sense
of [def-weil-pbc-bounded-constructible-tower] and put $M=R\lim M_\bullet$. Here $R\lim$ is total right derived inverse limit on the strict tower category, computed by a K-injective tower resolution and termwise inverse limit [lem-weil-pbc-ringed-strict-tower-homotopy-limit]; its natural Roos triangle realizes the object-only notation of [def-weil-pbc-derived-inverse-limit].
For every local model in [def-weil-pbc-bounded-constructible-tower],
restriction of the derived-limit projections gives a functorial isomorphism

$$
 L_{\alpha j}\xrightarrow{\sim}M|_{U_{\alpha j}}.
$$

Consequently $M$ is derived $I$-complete, the canonical maps

$$
 M\otimes_A^LP_n\xrightarrow{\sim}M_n
$$

are isomorphisms compatible with normalization, and $M$ has no cohomology
outside $[d_0,d_1]$. No finiteness assertion about the groups of sections on
$U_{\alpha j}$ is required.


 Here $M\otimes_A^LP_n$ means $M\otimes^L_{A_T}(P_n)_T$. Functoriality of the local isomorphism is for local models equipped with a derived-tower isomorphism lifting their specified level maps $e_n$; such a lift always exists, but is not asserted unique or chosen functorially. A morphism between equipped local models is a pair $(f,h)$ whose square with these derived-tower isomorphisms commutes. These conventions specify the coherent data needed to apply the strict derived-limit functor, for the stated functoriality.
```

Step 2, `def-weil-pbc-bounded-constructible-complete`:

```text
Let $\ell$ be a prime, let $E/\mathbf Q_\ell$ be a finite extension,
let $A=\mathcal O_E$ be its valuation ring with uniformizer $\varpi$, and
put $I=(\varpi)$ and $P_n=A/I^n$ for $n\geq1$. Let $T$ be a noetherian
scheme of finite dimension on which $\ell$ is invertible. Use $A_T$,
$D(T_{\Proet},A)$, and the normalized reduction tower $K_\bullet$ of
[def-weil-pbc-adic-coefficient-datum], with
$K_n=K\otimes^L_{A_T}(P_n)_T$.

Define $\Dbc(T_{\Proet},A)$ to be the full subcategory of
$D(T_{\Proet},A)$ consisting of objects $K$ which are derived $I$-complete
[def-weil-pbc-intrinsic-completion], whose reduction tower is uniformly
bounded constructible [def-weil-pbc-bounded-constructible-tower], and which
admit compatible etale-origin witnesses [def-weil-pbc-etale-origin-witness].
Here compatible witnesses mean objects $L_n\in D^+(T_{\Et},P_n)$,
isomorphisms $\alpha_n:\nu_T^*L_n\xrightarrow{\sim}K_n$, and isomorphisms
$\beta_n:L_{n+1}\otimes^L_{P_{n+1}}P_n\xrightarrow{\sim}L_n$ such that
$\alpha_n\circ\nu_T^*(\beta_n)$ equals the composite of
$\alpha_{n+1}\otimes^L P_n$ with the normalization isomorphism
$K_{n+1}\otimes^L_{P_{n+1}}P_n\xrightarrow{\sim}K_n$, using the canonical
identification of inverse image with coefficient reduction. The composites
for $P_m\to P_n$ satisfy the quotient cocycle. Membership requires the
existence of these compatible witnesses; morphisms are all morphisms of
$D(T_{\Proet},A)$ between the selected objects.

For comparison, Stacks Project Tag 09C1, proetale.tex,
Definition \texttt{definition-Dbc} in Section \texttt{section-suitable-derived}
(Tag 09C0), defines $D_{cons}(X,\Lambda)$ for a Noetherian ring $\Lambda$
and an ideal $I$ by derived completeness and constructible cohomology with
locally finite tor dimension of
$K\otimes^L_\Lambda\underline{\Lambda/I}$. That definition does not itself
identify its constant-coefficient category with the $A_T$-module category
and compatible uniform tower used here; no such identification is asserted
by this definition.
```

Step 2, `pqf-lem-locnoeth-lft`:

```text
If $S$ is
locally Noetherian and $f:X\to S$ is
locally of finite type, then $X$ is locally Noetherian.
(*Stacks Project, Morphisms of Schemes, Lemma 29.15.6, Tag
[01T6](https://stacks.math.columbia.edu/tag/01T6).*)
```

Step 2, `lem-weil-pbc-qcqs-over-affine`:

```text
Let $f:X\to Y$ be a morphism of schemes [def-pc-scheme] with $Y$ affine, for instance $Y=\operatorname{Spec}k$ for a field $k$ [def-weil-affine-spectrum]. If $f$ is quasi-compact [def-weil-finite-type-morphism] (in particular if $f$ is of finite type) and quasi-separated [def-weil-quasi-separated-morphism] (in particular if $f$ is separated [def-weil-proper-morphism]), then the scheme $X$ is quasi-compact (its underlying topological space is quasi-compact, i.e. $X\to\operatorname{Spec}\mathbf Z$ is quasi-compact) and quasi-separated ($X\to\operatorname{Spec}\mathbf Z$ is quasi-separated), conventions of [def-weil-pbc-scheme-conventions]. In particular a scheme separated and of finite type over a field is quasi-compact and quasi-separated.
```

Step 2, `lem-kun-dimension-finite-type`:

```text
Let $K$ be a field and $X$ a scheme of finite type over $K$.
Then $\kundim X<\infty$.
```

Step 3, `lem-weil-tower-category-levelwise-abelian`:

```text
Let $\mathcal A$ be an abelian category [def-sp-abelian] and let $\operatorname{Tow}(\mathcal A)$ be the category of inverse systems $(T_n,f_n:T_{n+1}\to T_n)_{n\geq1}$ in $\mathcal A$ with morphisms of inverse systems [def-weil-inverse-system], with the levelwise addition of morphisms $(\varphi+\psi)_n=\varphi_n+\psi_n$. Then $\operatorname{Tow}(\mathcal A)$ is an abelian category, and for every $n\geq1$ the evaluation functor $\operatorname{ev}_n:\operatorname{Tow}(\mathcal A)\to\mathcal A$, $(T_m)_m\mapsto T_n$, is additive and exact: finite products, kernels and cokernels of $\operatorname{Tow}(\mathcal A)$ are computed levelwise (the kernel of $\varphi:T\to T'$ is the system $(\ker\varphi_n)_n$ with the induced transition maps, and similarly for cokernels). In particular a morphism $\varphi$ of inverse systems is a monomorphism, resp. an epimorphism, if and only if every $\varphi_n$ is one, and a sequence $0\to T\to T'\to T''\to0$ in $\operatorname{Tow}(\mathcal A)$ is short exact if and only if $0\to T_n\to T'_n\to T''_n\to0$ is short exact in $\mathcal A$ for every $n$.
```

Step 3, `lem-weil-pbc-ringed-strict-tower-homotopy-limit`:

```text
Let $\mathcal C$ be a small site, $\mathcal O$ a sheaf of commutative rings, and $\mathcal A=\operatorname{Mod}(\mathcal O)$ [def-weil-sheaf-of-modules-category]. Let $\operatorname{Tow}(\mathcal A)=\operatorname{Fun}(\mathbf N_{\geq1}^{\mathrm{op}},\mathcal A)$, whose objects are strict inverse sequences and whose exactness is levelwise. On its derived category [def-weil-abstract-derived-category], total right derived inverse limit is computed by taking a K-injective tower resolution and then termwise inverse limit [def-pur-kinjective-complex]. This gives an exact functor $R\lim:D(\operatorname{Tow}(\mathcal A))\to D(\mathcal A)$. For every strict tower complex $X_\bullet$ there is a natural distinguished triangle $R\lim X_\bullet\to\prod_n^D X_n\xrightarrow{1-s}\prod_n^D X_n\to(R\lim X_\bullet)[1]$ [def-weil-derived-limit], where $\prod^D$ is the product in $D(\mathcal A)$ and the $n$-th component of $s$ is transition followed by projection to $n+1$. In particular, if for every $n$ some transition $X_m\to X_n$, $m\geq n$, is zero in $D(\mathcal A)$, then $R\lim X_\bullet=0$. If $v:X_\bullet\to Y_\bullet$ is a strict map of tower complexes whose tower of mapping cones has that property, then the canonical map $R\lim(v)$ is an isomorphism. No exactness of countable products in $\mathcal A$ is assumed.
```

Step 4, `lem-pur-condensed-exceptional-reconstruction`:

```text
Fix a prime $\ell$, a field $k$ of positive prime characteristic different from $\ell$, and a $k$-morphism $f:X\to Y$ between separated finite-type $k$-schemes [def-weil-pbc-scheme-conventions]. Put $\Omega=\overline{\mathbf Q}_\ell$ and $E=\mathbf Q_\ell$. On a scheme $T$ equal to $X$ or $Y$, write $\widehat{\mathbf Z}_{\ell,T}=\varprojlim_n (\mathbf Z/\ell^n\mathbf Z)_T$, and let $\mathcal I_T$ be the completed integral constructible category of [def-weil-pbc-bounded-constructible-complete] with coefficient ring $\mathbf Z_\ell$. Its rationalization has morphisms $\operatorname{Hom}(L,M)\otimes_{\mathbf Z_\ell}\mathbf Q_\ell$ [def-weil-pbc-rational-category]. Let $J_T:\mathcal I_T[1/\ell]\simeq\mathcal C^c_E(T)$ be the scalar-extension realization of [lem-weil-pbc-condensed-e-realization]. Let $E_T^c=p_T^*C(-,\mathbf Q_\ell)$ and $\Omega_T^c=p_T^*\underline\Omega$, where $\underline\Omega(S)$ consists of continuous maps on the profinite set $S$ with values in one finite intermediate field of $\Omega/E$, as in [def-weil-pbc-condensed-e-module-category, prop-weil-pbc-qbar-condensed-two-colimit]. Define the functor
$$U_T:\mathcal I_T\longrightarrow\mathcal C^c_\Omega(T),\qquad U_T(L)=\Omega_T^c\otimes^L_{E_T^c}J_T(L[1/\ell]).$$

For $L\in\mathcal I_Y$ put $L_n=L\otimes^L_{\widehat{\mathbf Z}_{\ell,Y}}(\mathbf Z/\ell^n\mathbf Z)_Y$. Let $Rf_n^!$ denote the constructible exceptional inverse image of [def-weil-exceptional-inverse-image]. Suppose supplied a strict derived tower $M_\bullet$ with level objects $M_n=Rf_n^!L_n$, normalization isomorphisms $M_{n+1}\otimes^L_{A_{n+1,X}}A_{n,X}\simeq M_n$ given by exceptional-image reduction, transition maps induced by these isomorphisms and the quotient maps, and the quotient cocycle, where $A_{n,T}=(\mathbf Z/\ell^n\mathbf Z)_T$. Suppose each cohomology sheaf of each level is constructible in the intrinsic finite-stratification sense of [def-weil-proetale-constructible-sheaf], and the levels have a common finite cohomological interval independent of $n$. Assume $M=R\varprojlim M_\bullet$ lies in $\mathcal I_X$, with its canonical reductions identified with $M_n$ [def-weil-pbc-adic-coefficient-datum, lem-weil-pbc-ringed-strict-tower-homotopy-limit]. Then there is a natural isomorphism
$$c_{f,L,M_\bullet}:U_X(M)\xrightarrow{\sim}Rf_{!,\Omega}^{\,R}(U_YL).$$
Here $Rf_{!,\Omega}$ is the bounded constructible condensed-module compact-support functor, defined using extension by zero and proper direct image in the chosen Nagata compactification, and $Rf_{!,\Omega}^{\,R}$ is its chosen right adjoint on $\mathcal C^c_\Omega$, namely $\mathrm{boundedConstructibleUpperShriek}(\mathrm{Profinite.padicAlgClRingObj}(\ell),\ell,f)$ at master commit 7347520d9b0d17cc31d0fc34ea20f1381a83fe13. More explicitly, if the chosen compactification is $X\xrightarrow{j}\overline X\xrightarrow{g}Y$, this right adjoint is $(Rg_{*,\Omega})^R$ followed by $j^*$, with the adjunction obtained by composing $j_!\dashv j^*$ and the chosen $Rg_{*,\Omega}\dashv(Rg_{*,\Omega})^R$. This assertion concerns this constructible right adjoint and asserts no unbounded ambient pro-etale adjoint. The isomorphism is the adjunction comparison: its counit is induced by the finite-level exceptional counits under completed reconstruction, localization and extension to $\Omega$. It is compatible with a refinement of the compactification and with morphisms of the supplied coherent systems. In addition $U_T$ sends the integral coefficient object to the condensed tensor unit and commutes with shifts.
```

Step 5, `lem-weil-pbc-condensed-point-basis-evaluation`:

```text
Use the universes of [def-weil-size-convention] and the small pro-etale site [def-weil-pbc-proetale-site]. Let $X$ be a scheme [def-pc-scheme], and let $p_X^*=\pi_X^{-1}a^*$ be the geometric inverse image from sheaves on profinite sets defined in [lem-weil-pbc-profinite-point-pullback]. Let $F$ be a sheaf of sets, abelian groups, or commutative rings on profinite sets with finite jointly surjective coverings. Let $U$ be an affine object of $X_{\mathrm{proet}}$ which is weakly contractible, meaning evaluation at $U$ sends epimorphisms of sheaves of sets to surjections. The quotient space $\pi_0(|U|)$ of connected components is profinite, and there is a canonical identification $(p_X^*F)(U)\cong F(\pi_0(|U|))$, natural in $F$ and in morphisms between such $U$. The identification preserves addition and multiplication when present. The topology on $\pi_0(|U|)$ is the quotient topology: a subset is open if and only if its inverse image in $|U|$ is open.
```

Step 5, `lem-weil-pbc-proetale-affine-wcontractible-covering-family`:

```text
Let $X$ be a scheme [def-pc-scheme] with its small pro-etale site $X_{\mathrm{proet}}$ [def-weil-pbc-proetale-site] and universes [def-weil-size-convention]. Every object $U$ of this site admits a covering family $\{U_i\to U\}_{i\in I}$ in which each $U_i$ is affine and weakly contractible for the full site $X_{\mathrm{proet}}$. Here weakly contractible means that for every epimorphism $F\to G$ of sheaves of sets on this site, $F(U_i)\to G(U_i)$ is surjective.
```

Step 5, `lem-pur-twist-sheaf-locally-free`:

```text
Fix a prime $\ell$, a finite extension $E/\Ql$ with valuation ring $\mathcal O_E$,
uniformizer $\varpi_E$ and residue rings $A_{E,n}=\mathcal O_E/\varpi_E^n$,
$n\geq1$ [def-weil-finite-field-fiber], and a scheme $S$ on which $\ell$ is
invertible. On the small pro-etale site [def-weil-pbc-proetale-site] of $S$,
let $\mu_{\ell^r,S}$ be the sheaf of $\ell^r$-th roots of unity with transition
maps $u\mapsto u^\ell$ [def-pur-roots-of-unity-sheaf], let $\varprojlim$ be
the inverse limit of sheaves [def-pur-sheaf-inverse-limit] and $\otimes$ the
tensor product of sheaves of modules [def-pur-sheaf-tensor-product], let
$\widehat{\Zl}_S=\varprojlim_r(\mathbf Z/\ell^r\mathbf Z)_S$ and
$\widehat{\mathcal O}_{E,S}=\varprojlim_n(A_{E,n})_S$ be the completed
coefficient sheaves [def-weil-completed-integral-coefficients], and put

$$
 \Zl(1)_S=\varprojlim_{r\geq1}\mu_{\ell^r,S},\qquad
 \mathcal O_E(1)_S=\Zl(1)_S\otimes_{(\Zl)_S}(\mathcal O_E)_S,\qquad
 A_{E,n}(1)_S=\mathcal O_E(1)_S\otimes_{(\mathcal O_E)_S}(A_{E,n})_S .
$$

Then:

1. For every $r\geq1$ there is an etale covering $\{U_i\to S\}$ such that
$\mu_{\ell^r,S}|_{U_i}\cong(\mathbf Z/\ell^r\mathbf Z)_{U_i}$ as sheaves of
$(\mathbf Z/\ell^r\mathbf Z)_{U_i}$-modules; so $\mu_{\ell^r,S}$ is a locally
constant sheaf with finite stalks, locally free of rank one over
$(\mathbf Z/\ell^r\mathbf Z)_S$, and the transition maps
$\mu_{\ell^{r+1},S}\to\mu_{\ell^r,S}$ are surjective.

2. $\Zl(1)_S$ is a sheaf of $\widehat{\Zl}_S$-modules, and there is a pro-etale
covering $\{V_j\to S\}$ with $\Zl(1)_S|_{V_j}\cong\widehat{\Zl}_{V_j}$; so
$\Zl(1)_S$ is locally free of rank one over $\widehat{\Zl}_S$, and
$\Zl(1)_S\otimes_{\widehat{\Zl}_S}(\mathbf Z/\ell^r\mathbf Z)_S\cong\mu_{\ell^r,S}$
for every $r$.

3. $\mathcal O_E$ being a free $\Zl$-module of finite rank,
$\widehat{\Zl}_S\otimes_{(\Zl)_S}(\mathcal O_E)_S\cong\widehat{\mathcal O}_{E,S}$,
and $\mathcal O_E(1)_S$ is a locally free $\widehat{\mathcal O}_{E,S}$-module of
rank one with
$\mathcal O_E(1)_S\otimes_{\widehat{\mathcal O}_{E,S}}(A_{E,n})_S\cong A_{E,n}(1)_S$,
a locally free $(A_{E,n})_S$-module of rank one, locally constant with finite
stalks, for every $n\geq1$.

4. With the integral derived reduction over the completed coefficient sheaf
[def-weil-integral-derived-reduction],
$\mathcal O_E(1)_S\otimes^L_{\mathcal O_E}A_{E,n}\cong A_{E,n}(1)_S$ placed in
degree $0$ for every $n\geq1$; $A_{E,n}(1)_S$ lies in $D^b_c(S,A_{E,n})$
[def-weil-finite-torsion-constructibility] with cohomological support [def-weil-cohomological-support] contained in
$\{0\}$ (equal to $\{0\}$ when $S$ is nonempty);
$\mathcal O_E(1)_S$ is derived complete [def-weil-derived-complete]; hence
$\mathcal O_E(1)_S$ lies in the derived-complete integral category
$D^b_c(S,\mathcal O_E)$ [def-weil-derived-complete-integral-detailed].
```

Step 5, `lem-weil-pbc-reconstruction-uniform-tower`:

```text
Let $k$ be a field and let $T$ be a scheme of finite type over $\operatorname{Spec}k$ [def-weil-finite-type-morphism]. Let $M_\bullet$ be a uniformly bounded constructible adic tower in the sense
of [def-weil-pbc-bounded-constructible-tower] and put $M=R\lim M_\bullet$. Here $R\lim$ is total right derived inverse limit on the strict tower category, computed by a K-injective tower resolution and termwise inverse limit [lem-weil-pbc-ringed-strict-tower-homotopy-limit]; its natural Roos triangle realizes the object-only notation of [def-weil-pbc-derived-inverse-limit].
For every local model in [def-weil-pbc-bounded-constructible-tower],
restriction of the derived-limit projections gives a functorial isomorphism

$$
 L_{\alpha j}\xrightarrow{\sim}M|_{U_{\alpha j}}.
$$

Consequently $M$ is derived $I$-complete, the canonical maps

$$
 M\otimes_A^LP_n\xrightarrow{\sim}M_n
$$

are isomorphisms compatible with normalization, and $M$ has no cohomology
outside $[d_0,d_1]$. No finiteness assertion about the groups of sections on
$U_{\alpha j}$ is required.


 Here $M\otimes_A^LP_n$ means $M\otimes^L_{A_T}(P_n)_T$. Functoriality of the local isomorphism is for local models equipped with a derived-tower isomorphism lifting their specified level maps $e_n$; such a lift always exists, but is not asserted unique or chosen functorially. A morphism between equipped local models is a pair $(f,h)$ whose square with these derived-tower isomorphisms commutes. These conventions specify the coherent data needed to apply the strict derived-limit functor, for the stated functoriality.
```

Step 5, `lem-weil-pbc-condensed-e-realization`:

```text
Let $\ell$ be prime, let $E/\mathbf Q_\ell$ be a finite normed field extension, and let $k$ be a field of positive prime characteristic different from $\ell$. Let $\mathcal O_E$ be the valuation ring of $E$ and fix a uniformizer $\varpi$. For every separated finite-type $k$-scheme $T$, let $\mathcal R_T(E)=\Dbc(T,\mathcal O_E)[1/\varpi]$ be the raw rationalized category of [def-weil-pbc-rational-category], whose integral category is [def-weil-pbc-bounded-constructible-complete], and let $\mathcal C_T^c(E)$ and $E_T^c$ be the module-object category and coefficient ring of [def-weil-pbc-condensed-e-module-category]. There is a canonical ring-sheaf isomorphism
$$E_T^c\cong\bigl(V\mapsto C(|V|,E)\bigr)$$
(here $V\to T$ is an object of the small pro-etale site, $|V|$ is the entire underlying Zariski topological space of $V$, and $C(|V|,E)$ denotes continuous functions to the normed field $E$, with pointwise ring operations and restriction by precomposition), and an $E$-linear equivalence $J_T:\mathcal R_T(E)\simeq\mathcal C_T^c(E)$ induced by derived extension of scalars from the completed integral coefficient sheaf to this ring sheaf. In particular the archived criterion of stratified local finite presentation agrees, after finite refinement of the stratification if necessary, with bounded cohomology that is stratified locally free of finite rank over the continuous $E$-coefficient sheaf; every object of $\mathcal C_T^c(E)$ is isomorphic to $J_T(M)$ for an integral constructible complex $M$ viewed in $\mathcal R_T(E)$.

For every $k$-morphism $h:T\to U$ between such schemes, the ambient condensed-module functors $Lh_c^*$ and $Rh_{c,*}$ preserve $\mathcal C^c(E)$ and have natural comparison isomorphisms
$$J_TLh_{\mathrm{rat}}^*\cong Lh_c^*J_U,\qquad J_URh_{\mathrm{rat},*}\cong Rh_{c,*}J_T,$$
where the rational functors are those of [prop-weil-pbc-rational-transport]. These comparisons preserve the units and counits of the pullback/direct-image adjunctions: inserting a rational unit and then applying $J$ gives the condensed unit under the displayed comparisons, and the same holds for counits. They preserve the identity and composition isomorphisms of pullbacks. Thus the comparison obtained from pullback composition and the equality of two composite scheme morphisms corresponds to the same comparison in the condensed categories. These assertions concern categories, individual functors and their adjunction and composition structures, and impose no cartesian-square or properness hypothesis.

For a cartesian square of these schemes with arrows $f:X\to Y$, $g:Y'\to Y$, $f':X'\to Y'$ and $g':X'\to X$, and with $f$ proper and any integral bounded constructible $M$, the rationalization of the specified ordered completed exchange of [def-weil-pbc-completed-base-change-map] is the unit-square-counit mate for the rationalized adjunctions just described. Its image under $J_{Y'}$, conjugated by the displayed pullback and direct-image comparisons, is the restricted condensed unit-square-counit exchange of [def-weil-pbc-condensed-e-module-category] at $J_XM$. This is an equality of the specified transformations, not just an isomorphism between their sources and targets; no invertibility of exchange is asserted here.
```

Step 5, `prop-weil-pbc-qbar-condensed-two-colimit`:

```text
Fix a prime $\ell$, write $\Omega=\overline{\mathbf Q}_\ell$ [def-weil-l-adic-numbers, def-weil-algebraic-closure], and order its finite intermediate extensions $E/\mathbf Q_\ell$ by inclusion [def-weil-finite-subextension-directed-set]. Use the condensed rings $\underline E(S)=C(S,E)$ on profinite sets and the coefficient pullback $p_T^*$ of [def-weil-pbc-condensed-e-module-category]. Define $\underline\Omega(S)$ to be the subring of $C(S,\Omega)$ consisting of continuous functions whose values lie in one finite intermediate extension, with restrictions by precomposition. Thus $\underline\Omega$ is the archived $\mathrm{Profinite.padicAlgClRingObj}(\ell)$, not the full continuous-function sheaf. Put $E_T^c=p_T^*\underline E$ and $\Omega_T^c=p_T^*\underline\Omega$. Write $\mathcal C_E^c(T)$ for the bounded constructible module-object category of [def-weil-pbc-condensed-e-module-category], and define $\mathcal C_\Omega^c(T)$ by the identical construction with coefficient ring $\Omega_T^c$: a full subcategory of $D(\operatorname{Mod}_{\Omega_T^c})$, with bounded cohomology, each cohomology sheaf stratified pro-etale locally finitely presented. No derived completeness condition is imposed. Let $T_{E,F}^T=F_T^c\otimes^L_{E_T^c}-$ and $T_{E,\Omega}^T=\Omega_T^c\otimes^L_{E_T^c}-$ denote derived extension of scalars along the coefficient inclusions. Let $T$ be a scheme [def-pc-scheme] whose underlying space is noetherian (every ascending chain of open subsets stabilizes). These scalar extensions preserve the displayed bounded constructible categories and have the canonical tensor-transitivity comparisons. The cocone with vertex $\mathcal C_\Omega^c(T)$ is a filtered two-colimit: its comparison functor sends $(E,K_E)$ to $T_{E,\Omega}^T K_E$ and is an equivalence. Here the source pair category has objects $(E,K_E)$ with $K_E\in\mathcal C_E^c(T)$ and morphisms represented by maps $T_{E,H}^T K_E\to T_{F,H}^T L_F$ at finite $H\supseteq E,F$, modulo equality after further scalar extension, with composition at a common finite overfield using tensor associativity. Explicitly, every object of $\mathcal C_\Omega^c(T)$ is isomorphic to some $T_{E,\Omega}^T K_E$; every morphism between two such objects descends to a common finite overfield; and two finite-stage morphisms with equal images become equal after a further finite extension. These finite-stage categories are condensed module-object categories, not the raw rationalizations of integral categories.
```

## Exact master source exhibits

All files below are the complete, verbatim UTF-8 blob contents at commit `7347520d9b0d17cc31d0fc34ea20f1381a83fe13`. Paths are relative to that source tree. These copied reference texts are not proofs or authored Lean changes; their existing sorry bodies remain visible. They provide local source access inside the committed report, independently of any missing literature mirror. Git blob hashes include the standard blob header; SHA-256 hashes cover the unmodified UTF-8 file bytes.

Source `WeilConjectures/SmoothPurity/Defs.lean`

Git blob: `76353ea24654c774ec24d7fedffdd65edcb30666`; SHA-256: `8eac98029064bdc002a3e1c36fffcb3c2c86868e492f6545774071599a7fcb9c`.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.TateTwist.ProEtale

/-!

# Smooth purity for `ℚ̄_ℓ`-coefficients on the pro-étale site

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. As in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all schemes are
objects `X : Over (Spec (.of k))`, separated and of finite type over `Spec k`, and all morphisms
are morphisms `f : X ⟶ Y` of `Over (Spec (.of k))`; in particular `ℓ` is invertible on every
scheme considered. In the documentation, `X` also stands for the underlying scheme `X.left`.

Let `f : X ⟶ Y` be a morphism whose underlying morphism of schemes `f.left` is smooth of pure
relative dimension `d`. *Smooth purity* (SGA 4, Exposé XVIII, Théorème 3.2.5, and Bhatt–Scholze,
*The pro-étale topology for schemes*, Section 6.8, for `ℚ̄_ℓ`-coefficients) identifies the
exceptional inverse image of the constant coefficient object with a shifted Tate twist:
```
pur_f : Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]
```
in the derived category `D(Mod_{ℚ̄_ℓ,X})` of module objects over `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ`, the
pullback of the condensed ring `ℚ̲̄_ℓ` (`Profinite.padicAlgClRingObj ℓ`). Here `Rf^!` is
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriek` on the bounded
constructible derived categories `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` (the right adjoint of `Rf_!`, built from the
compactification of `f` chosen by Nagata's theorem), `ℚ̄_ℓ,Y` is the tensor unit of the
monoidal category `Dᵇc(Y)⟦ℚ̲̄_ℓ⟧`
(`AlgebraicGeometry.ProEtale.CondensedRing.isMonoidal_boundedConstructible`), whose underlying
complex is the tensor unit of `D(Mod_{ℚ̄_ℓ,Y})`, and `ℚ̄_ℓ,X(d)` is the Tate twist of
`WeilConjectures.TateTwist.ProEtale`. The isomorphism is stated after the inclusion
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ D(Mod_{ℚ̄_ℓ,X})`, which is fully faithful, so that the constructibility of the Tate
twists need not be recorded.

## Sorried data

`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso` is the purity isomorphism, stated as a
`@[no_expose]` definition with value `sorry`: it is a *chosen* isomorphism, which downstream
constructions (the trace map and Poincaré duality, see
`WeilConjectures/PoincareDuality/Instruction.tex`) use as data, and whose normalization they
inherit.

The isomorphism is not a canonical map whose invertibility could be stated as a proposition
with the tools currently available: classically it is the adjoint of the trace map
`Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y` of SGA 4, Exposé XVIII, whose construction (by reduction to
relative curves and the cycle class of the diagonal) is not formalized. Its intended
normalization and compatibilities — with composition of smooth morphisms, with base change,
with étale maps (where `d = 0` and `pur` is the identification `Rf^! = Lf^*`), and the
identification of the induced trace with the classical trace on `H^{2d}_c` of a smooth curve —
are therefore not stated here either.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Smooth purity -/

section Purity

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]

/-- **Smooth purity**: for a morphism `f : X ⟶ Y` of separated `k`-schemes of finite type
which is smooth of pure relative dimension `d`, the exceptional inverse image of the constant
coefficient object is the shifted Tate twist, `Rf^! ℚ̄_ℓ,Y ≅ ℚ̄_ℓ,X(d)[2d]`. This is a chosen
isomorphism: see the module docstring. -/
@[no_expose]
noncomputable def smoothPurityIso :
    ((boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
      (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))).obj ≅
      (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d) :=
  sorry

end Purity

end AlgebraicGeometry.ProEtale.CondensedRing
````

Source `WeilConjectures/TateTwist/ProEtale.lean`

Git blob: `b26295f63a04264246319a1fd5f8b4f6421eb78c`; SHA-256: `b9554907baced298abbb0648fe084ac9eaffcf576c4e03e6f26a90ff3f0fff2f`.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.TateTwist.RootsOfUnity

/-!

# Tate twists of the `ℚ̄_ℓ`-sheaf on the pro-étale site

Let `ℓ` be a prime and `X` a scheme. This file constructs the Tate twists `ℚ̄_ℓ,X(d)`,
`d ∈ ℤ`, as module objects over the coefficient ring object `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ`
(`AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) X`) of abelian
sheaves on `X_proét`, the pullback of the condensed ring `ℚ̲̄_ℓ` of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` along `p_X : X_proét ⟶ *_proét`,
following Bhatt–Scholze, *The pro-étale topology for schemes*, Section 6.8:
```
ℤ_ℓ(1) := lim_n μ_{ℓ^n},     ℚ̄_ℓ(1) := ℚ̄_ℓ ⊗_{ℤ_ℓ} ℤ_ℓ(1),
```
where `ℤ_ℓ = ℤ_ℓ,X = p_X^* ℤ̲_ℓ` is the pullback of the condensed ring `ℤ̲_ℓ = C(-, ℤ_ℓ)`.

## The construction

* The `ℤ_ℓ,X`-module `ℤ/ℓ^n(1)` is the free module `ℤ_ℓ,X ⊗ μ_{ℓ^n}` on the sheaf `μ_{ℓ^n}` of
  `ℓ^n`-th roots of unity (`AlgebraicGeometry.ProEtale.rootsOfUnitySheaf`), the tensor product
  being the sheafified tensor product of abelian sheaves. Since `μ_{ℓ^n}` is killed by `ℓ^n`, this
  is `ℤ/ℓ^n ⊗_{ℤ/ℓ^n} μ_{ℓ^n} = μ_{ℓ^n}` as an abelian sheaf, with its natural structure of a
  module over `ℤ_ℓ,X ⟶ ℤ/ℓ^n` (`AlgebraicGeometry.ProEtale.tateModuleLevel`). Taking the free
  module avoids defining the action of `ℤ_ℓ,X` on `μ_{ℓ^n}` by hand.
* `ℤ_ℓ(1)` is the limit, in the category of `ℤ_ℓ,X`-module objects, of the inverse system
  `ℤ_ℓ ⊗ μ_{ℓ^{n+1}} ⟶ ℤ_ℓ ⊗ μ_{ℓ^n}` induced by the `ℓ`-th power maps
  (`AlgebraicGeometry.ProEtale.tateModule`).
* `ℚ̄_ℓ(1)` is the extension of scalars of `ℤ_ℓ(1)` along the coefficient change
  `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X` (`AlgebraicGeometry.ProEtale.coefficientMap`), the pullback along `p_X` of the
  inclusion `ℤ̲_ℓ ⟶ ℚ̲̄_ℓ` of condensed rings (`Profinite.padicIntRingObjToPadicAlgCl`), i.e. the
  relative tensor product `ℚ̄_ℓ,X ⊗_{ℤ_ℓ,X} ℤ_ℓ(1)` (`AlgebraicGeometry.ProEtale.tateTwistOne`).
  The tensor product has to be taken over `ℤ_ℓ,X` and not over `ℤ`: `ℚ̄_ℓ ⊗_ℤ μ_{ℓ^n} = 0`, and
  `ℚ̄_ℓ ⊗_ℤ ℤ_ℓ(1)` is much larger than `ℚ̄_ℓ(1)`.
* For `d ≥ 0`, `ℚ̄_ℓ(d)` is the `d`-th tensor power of `ℚ̄_ℓ(1)` over `ℚ̄_ℓ,X`, and for `d < 0`
  it is the dual `Hom_{ℚ̄_ℓ}(ℚ̄_ℓ(-d), ℚ̄_ℓ)` (`AlgebraicGeometry.ProEtale.tateTwist`).

Finally `ℚ̄_ℓ,X(d)` is placed in degree `0` of the derived category `D(Mod_{ℚ̄_ℓ,X})`
(`AlgebraicGeometry.ProEtale.tateTwistDerived`), and the twist functor `K ↦ K(d)` on
`D(Mod_{ℚ̄_ℓ,X})` is the derived tensor product with it
(`AlgebraicGeometry.ProEtale.tateTwistFunctor`).

## Implementation notes

* The construction is functorial in nothing: the comparisons `f^* ℚ̄_ℓ,Y(d) ≅ ℚ̄_ℓ,X(d)`, the
  invertibility `ℚ̄_ℓ(d) ⊗ ℚ̄_ℓ(e) ≅ ℚ̄_ℓ(d + e)` and the local triviality of `ℚ̄_ℓ(1)` when `ℓ`
  is invertible on `X` are not stated here.
* The Galois (Frobenius) action on `ℚ̄_ℓ(1)` for `X` over a finite field, which is what
  distinguishes `ℚ̄_ℓ(d)` from `ℚ̄_ℓ` over a separably closed field, is part of the Weil sheaf
  formalism and is not considered.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory MonObj Limits

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The inclusion `ℤ̲_ℓ ⟶ ℚ̲̄_ℓ` -/

/-- The inclusion `ℤ_ℓ ⊆ ℚ_ℓ`, as a ring homomorphism into the bottom finite subextension
`ℚ_ℓ ⊆ ℚ̄_ℓ`. -/
noncomputable def padicIntToBotFiniteIntermediateField :
    ℤ_[ℓ] →+* (⟨⊥, inferInstance⟩ : PadicAlgCl.FiniteIntermediateField ℓ) :=
  (algebraMap ℚ_[ℓ] (⊥ : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))).comp PadicInt.Coe.ringHom

lemma continuous_padicIntToBotFiniteIntermediateField :
    Continuous (padicIntToBotFiniteIntermediateField ℓ) :=
  continuous_induced_rng.2
    ((continuous_algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp continuous_subtype_val)

/-- The inclusion `ℤ̲_ℓ ⟶ ℚ̲̄_ℓ` of condensed rings: a continuous map `S → ℤ_ℓ` is a section of
`ℚ̲̄_ℓ` over `S`, with values in the finite subextension `ℚ_ℓ`. -/
noncomputable def padicIntCondensedRingToPadicAlgCl :
    padicIntCondensedRing.{u} ℓ ⟶ padicAlgClCondensedRing ℓ :=
  continuousMapRingSheafMap (padicIntToBotFiniteIntermediateField ℓ)
      (continuous_padicIntToBotFiniteIntermediateField ℓ) ≫
    padicSubfieldCondensedRingToPadicAlgCl ℓ ⟨⊥, inferInstance⟩

/-- The inclusion `ℤ̲_ℓ ⟶ ℚ̲̄_ℓ` of ring objects of condensed abelian groups: the abelian sheaf
morphism underlying `Profinite.padicIntCondensedRingToPadicAlgCl`. -/
noncomputable def padicIntRingObjToPadicAlgCl :
    continuousMapRingObj.{u} ℤ_[ℓ] ⟶ padicAlgClRingObj ℓ :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicIntCondensedRingToPadicAlgCl ℓ)

instance : IsMonHom (padicIntRingObjToPadicAlgCl.{u} ℓ) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (padicIntCondensedRingToPadicAlgCl ℓ)))

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The Tate module `ℤ_ℓ(1)` -/

/-- The `ℤ_ℓ,X`-module `ℤ/ℓ^n(1) = ℤ_ℓ,X ⊗ μ_{ℓ^n}`: the free `ℤ_ℓ,X`-module on the sheaf of
`ℓ^n`-th roots of unity, where `ℤ_ℓ,X = p_X^* ℤ̲_ℓ`. As an abelian sheaf it is `μ_{ℓ^n}`, since
`μ_{ℓ^n}` is killed by `ℓ^n`. -/
noncomputable def tateModuleLevel (n : ℕ) :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) :=
  (Mod.freeFunctor _).obj (rootsOfUnitySheaf X (ℓ ^ n))

/-- The transition map `ℤ/ℓ^{n+1}(1) ⟶ ℤ/ℓ^n(1)` of the Tate module, induced by the `ℓ`-th
power map `μ_{ℓ^{n+1}} ⟶ μ_{ℓ^n}`. -/
noncomputable def tateModuleTransition (n : ℕ) :
    tateModuleLevel X ℓ (n + 1) ⟶ tateModuleLevel X ℓ n :=
  (Mod.freeFunctor _).map (eqToHom (by rw [pow_succ']) ≫ rootsOfUnitySheafPow X (ℓ ^ n) ℓ)

/-- The inverse system `n ↦ ℤ/ℓ^n(1)` of `ℤ_ℓ,X`-modules. -/
noncomputable def tateModuleSystem :
    ℕᵒᵖ ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) :=
  Functor.ofOpSequence (tateModuleTransition X ℓ)

/-- The Tate module `ℤ_ℓ(1) = lim_n μ_{ℓ^n}` on `X_proét`, as a module object over `ℤ_ℓ,X`: the
limit of the inverse system `n ↦ ℤ/ℓ^n(1)`. -/
noncomputable def tateModule :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) :=
  limit (tateModuleSystem X ℓ)

/-! ### The Tate twists `ℚ̄_ℓ(d)` -/

/-- The Tate twist `ℚ̄_ℓ,X(1) = ℚ̄_ℓ,X ⊗_{ℤ_ℓ,X} ℤ_ℓ(1)`: the extension of scalars of the Tate
module along the coefficient change `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X`. -/
noncomputable def tateTwistOne :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) :=
  (Mod.extendScalars (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl ℓ) X)).obj
    (tateModule X ℓ)

/-- The non-negative Tate twists `ℚ̄_ℓ,X(d) = ℚ̄_ℓ,X(1)^{⊗ d}`, the tensor powers over `ℚ̄_ℓ,X`,
with `ℚ̄_ℓ,X(0) = ℚ̄_ℓ,X`. -/
noncomputable def tateTwistNat :
    ℕ → Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
  | 0 => 𝟙_ _
  | d + 1 => tateTwistNat d ⊗ tateTwistOne X ℓ

/-- The Tate twist `ℚ̄_ℓ,X(d)` for `d ∈ ℤ`: the tensor power `ℚ̄_ℓ,X(1)^{⊗ d}` for `d ≥ 0`, and
the dual `Hom_{ℚ̄_ℓ,X}(ℚ̄_ℓ,X(-d), ℚ̄_ℓ,X)` for `d < 0`. -/
noncomputable def tateTwist :
    ℤ → Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
  | (d : ℕ) => tateTwistNat X ℓ d
  | .negSucc d => (ihom (tateTwistNat X ℓ (d + 1))).obj (𝟙_ _)

lemma tateTwist_natCast (d : ℕ) : tateTwist X ℓ d = tateTwistNat X ℓ d := rfl

/-- The Tate twist `ℚ̄_ℓ,X(d)`, placed in degree `0` of the derived category
`D(Mod_{ℚ̄_ℓ,X})`. -/
noncomputable def tateTwistDerived (d : ℤ) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) :=
  (DerivedCategory.singleFunctor _ 0).obj (tateTwist X ℓ d)

/-- The Tate twist functor `K ↦ K(d) = K ⊗ᴸ_{ℚ̄_ℓ,X} ℚ̄_ℓ,X(d)` on `D(Mod_{ℚ̄_ℓ,X})`. -/
noncomputable def tateTwistFunctor (d : ℤ) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) :=
  tensorRight (tateTwistDerived X ℓ d)

end AlgebraicGeometry.ProEtale
````

Source `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/UpperShriek.lean`

Git blob: `197c2b7f9a750bfa107231bd4dc190d284a023c1`; SHA-256: `c27c43dce9fe3ca5742e1723242e05667eab9f7496c710376807e29490b9e245`.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!

# The exceptional inverse image on bounded constructible module objects

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`. As in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all schemes are
separated and of finite type over `Spec k`, and all morphisms are morphisms of
`Over (Spec (.of k))`.

The exceptional inverse image `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` is constructed on the bounded
constructible derived categories directly, out of the two halves of the derived lower shriek
attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:
```
Rf_!(c) := i_! ⋙ Rg_*,      Rf^!(c) := Rg^! ⋙ i^*,
```
where `i_! ⊣ i^*` is the adjunction along the open immersion `i` on bounded constructible
complexes (`boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction`) and `Rg^!` is a
chosen right adjoint of the bounded constructible pushforward `Rg_*` along the proper `g`. The
adjunction `Rf_!(c) ⊣ Rf^!(c)` is the composite of these two adjunctions.

The only input is that `Rg_* : Dᵇc(Z)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` is a left adjoint for proper `g`. The
constructions take it as an instance argument, and it is assumed (`sorry`) for the `ℓ`-adic
coefficient rings only: the condensed ring `E̲ = C(-, E)` of a finite extension `E` of `ℚ_ℓ`
(`Profinite.continuousMapRingObj E`), the condensed ring `𝒪̲_E = C(-, 𝒪_E)` of its ring of
integers, for `E ⊆ ℚ̄_ℓ` (`Profinite.padicIntegersRingObj ℓ E`), and the condensed ring `ℚ̲̄_ℓ`
(`Profinite.padicAlgClRingObj ℓ`).

Exactly as the lower shriek `boundedConstructibleLowerShriek`, the functor `Rf^!` is `Rf^!(c)`
for the compactification `c = compactificationOverField f` chosen by Nagata's theorem, and the
adjunction `Rf_! ⊣ Rf^!` is the adjunction `Rf_!(c) ⊣ Rf^!(c)`.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleUpperShriekOfCompactification`: `Rf^!(c)` on
  bounded constructible complexes, right adjoint to the lower shriek
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactification` of
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, and
  `ProEtale.CondensedRing.boundedConstructibleUpperShriekOfCompactificationAdjunction`: the
  adjunction `Rf_!(c) ⊣ Rf^!(c)`.
- `ProEtale.CondensedRing.boundedConstructibleUpperShriek`: `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` for
  the chosen compactification, and
  `ProEtale.CondensedRing.boundedConstructibleUpperShriekAdjunction`: the adjunction
  `Rf_! ⊣ Rf^!`.

## Sorried input

- `ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj`:
  for `g` proper, `Rg_*` on bounded constructible `E`-sheaves is a left adjoint.
- `ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj`:
  for `g` proper, `Rg_*` on bounded constructible `𝒪_E`-sheaves is a left adjoint.
- `ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`:
  for `g` proper, `Rg_*` on bounded constructible `ℚ̄_ℓ`-sheaves is a left adjoint.

## Implementation notes

`Rg^!` for proper `g` is `Functor.rightAdjoint`, an arbitrary choice of right adjoint extracted
from the instance, not a construction. Only the adjunction `Adjunction.ofIsLeftAdjoint` should be
used about it.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### The adjunction along a compactification -/

section OfCompactification

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

variable [(boundedConstructibleLowerStar Λ ℓ c.overG).IsLeftAdjoint]

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on bounded constructible complexes: a chosen right adjoint `Rg^!`
of the derived pushforward `Rg_*` along the proper `g`, followed by the pullback `i^*` along the
open immersion `i`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactification :
    Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructibleLowerStar Λ ℓ c.overG).rightAdjoint ⋙
    boundedConstructibleUpperStar Λ ℓ c.overI

/-- The adjunction `Rf_!(c) ⊣ Rf^!(c)` on bounded constructible complexes attached to a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`: the composite of the adjunction `i_! ⊣ i^*`
along the open immersion `i` and of the adjunction `Rg_* ⊣ Rg^!` along the proper `g`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactificationAdjunction :
    boundedConstructibleLowerShriekOfCompactification Λ ℓ c ⊣
      boundedConstructibleUpperShriekOfCompactification Λ ℓ c :=
  (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ c.overI).comp
    (Adjunction.ofIsLeftAdjoint _)

end OfCompactification

/-! ### The adjunction `Rf_! ⊣ Rf^!` -/

section Chosen

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

variable [(boundedConstructibleLowerStar Λ ℓ (compactificationOverField f).overG).IsLeftAdjoint]

/-- The exceptional inverse image `Rf^! : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible
complexes: the functor `boundedConstructibleUpperShriekOfCompactification` attached to the chosen
compactification `compactificationOverField f`. -/
noncomputable def boundedConstructibleUpperShriek : Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  boundedConstructibleUpperShriekOfCompactification Λ ℓ (compactificationOverField f)

/-- The adjunction `Rf_! ⊣ Rf^!` on bounded constructible complexes: the adjunction
`Rf_!(c) ⊣ Rf^!(c)` for the chosen compactification `c = compactificationOverField f`. -/
noncomputable def boundedConstructibleUpperShriekAdjunction :
    boundedConstructibleLowerShriek Λ ℓ f ⊣ boundedConstructibleUpperShriek Λ ℓ f :=
  boundedConstructibleUpperShriekOfCompactificationAdjunction Λ ℓ
    (compactificationOverField f)

/-- The derived lower shriek `Rf_!` on bounded constructible complexes is a left adjoint, its
right adjoint being `boundedConstructibleUpperShriek`. -/
instance isLeftAdjoint_boundedConstructibleLowerShriek :
    (boundedConstructibleLowerShriek Λ ℓ f).IsLeftAdjoint :=
  (boundedConstructibleUpperShriekAdjunction Λ ℓ f).isLeftAdjoint

instance isRightAdjoint_boundedConstructibleUpperShriek :
    (boundedConstructibleUpperShriek Λ ℓ f).IsRightAdjoint :=
  (boundedConstructibleUpperShriekAdjunction Λ ℓ f).isRightAdjoint

end Chosen

/-! ### The proper pushforward for the `ℓ`-adic coefficient rings -/

section EllAdic

include k

variable {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]

/-- For a proper morphism `g : Z ⟶ Y` and a finite extension `E` of `ℚ_ℓ`, the derived
pushforward `Rg_* : Dᵇc(Z)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` on bounded constructible `E`-sheaves is a left
adjoint; its right adjoint is the exceptional inverse image `Rg^!` along `g`. -/
instance isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ g).IsLeftAdjoint :=
  sorry

/-- For a proper morphism `g : Z ⟶ Y` and a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the derived
pushforward `Rg_* : Dᵇc(Z)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` on bounded constructible `𝒪_E`-sheaves is a
left adjoint; its right adjoint is the exceptional inverse image `Rg^!` along `g`. -/
instance isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructibleLowerStar (Profinite.padicIntegersRingObj ℓ E) ℓ g).IsLeftAdjoint :=
  sorry

/-- For a proper morphism `g : Z ⟶ Y`, the derived pushforward
`Rg_* : Dᵇc(Z)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` on bounded constructible `ℚ̄_ℓ`-sheaves is a left adjoint;
its right adjoint is the exceptional inverse image `Rg^!` along `g`. -/
instance isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj :
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ g).IsLeftAdjoint :=
  sorry

end EllAdic

end AlgebraicGeometry.ProEtale.CondensedRing
````

Source `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean`

Git blob: `503a487318229b2536a916d6a4e164468e64d1ec`; SHA-256: `dfcc5877cbb6fb4eaba57e32455b682ecc604955b5fa4d1ff951b927f94e7597`.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Compactification.Over
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek

/-!

# The six functors on bounded constructible module objects over `Λ`

Let `Λ` be a commutative condensed ring. For a scheme `X`, the bounded constructible derived
category `D_cons(X_proét, Λ_X)` of module objects over the coefficient ring object
`Λ_X = p_X^* Λ` is the full subcategory
`ProEtale.BoundedConstructible (condensedRingObj Λ X)` of `D(Mod_{Λ_X})`
(`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`), with scoped notation
`Dᵇc(X)⟦Λ⟧`. This file restricts the six functors on `D(Mod_{Λ_X})` of the folder
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived` to these full subcategories.

## The setting

Following Bhatt–Scholze, Section 6.8, in the simplified setting of schemes over a field: fix a
prime `ℓ` and a field `k` of characteristic `p > 0` with `p ≠ ℓ`
(`[Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`). All schemes are separated and of finite
type over `Spec k`: they are objects `X : Over (Spec (.of k))` of the category of schemes over
`Spec k`, with structure morphism `X.hom` locally of finite type, quasi-compact and separated.
All morphisms are morphisms `f : X ⟶ Y` of `Over (Spec (.of k))`, and the functors are those of
the underlying morphism of schemes `f.left`. In the documentation, `X` also stands for the
underlying scheme `X.left`, so that for instance `Dᵇc(X)⟦Λ⟧` is `Dᵇc(X.left)⟦Λ⟧` in the code.
No further hypothesis is imposed on the schemes or morphisms. In particular every such morphism
has a compactification, by Nagata's theorem (`AlgebraicGeometry.HasCompactification.of_over`),
with the choice `compactificationOverField f`. A compactification
`c = (X.left ⟶[i] Z ⟶[p] Y.left)` of `f.left` is a factorization in `Over (Spec (.of k))`,
through the object `c.overObj` and the morphisms `c.overI` and `c.overG` of
`WeilConjectures.Compactification.Over`.

| functor | restriction |
| --- | --- |
| `Lf^* = L((f)^*⟦Λ⟧)` | `boundedConstructibleUpperStar` |
| `Rf_* = R((f)_*⟦Λ⟧)` | `boundedConstructibleLowerStar` |
| `j_! = D((j)_!open⟦Λ⟧)`, `j` an open immersion | `boundedConstructibleOpenImmersionLowerShriek` |
| `- ⊗ᴸ -` | `boundedConstructibleTensor` |
| `RHom(-, -)` | `boundedConstructibleHom` |

The pullback, the pushforward and the extension by zero are the `ObjectProperty.lift` of the
composite of the inclusion with the functor on the ambient derived category, so they are
compatible with the inclusions by construction (`ObjectProperty.liftCompιIso`). The derived
tensor product and the derived hom are instead the monoidal closed structure of the full
subcategory `Dᵇc(X)⟦Λ⟧` (`ObjectProperty.fullMonoidalSubcategory`,
`ObjectProperty.fullMonoidalClosedSubcategory`), given by the instances
`isMonoidal_boundedConstructible` and `isMonoidalClosed_boundedConstructible`; they are again
compatible with the inclusions, the inclusion being strict monoidal (`ObjectProperty.monoidalι`).

The derived lower shriek is not a restriction: it is assembled on bounded constructible
complexes out of the functors above. For a compactification `c = (X ⟶[i] Z ⟶[p] Y)` of `f`,
`Rf_!^c := i_! ⋙ Rp_*` (`boundedConstructibleLowerShriekOfCompactification`), and `Rf_!` is
`Rf_!^c` for the chosen compactification `compactificationOverField f`
(`boundedConstructibleLowerShriek`). Both are compatible with the derived lower shrieks
`Rf_!(c)⟦Λ⟧` and `R(f)_!⟦Λ⟧` on the ambient derived categories
(`boundedConstructibleLowerShriekOfCompactificationCompatibility`,
`boundedConstructibleLowerShriekCompatibility`).

The adjunctions `Lf^* ⊣ Rf_*` and `j_! ⊣ j^*` restrict along the fully faithful inclusions
(`Adjunction.restrictFullyFaithful`), and so does the composition isomorphism
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` (`boundedConstructibleUpperStarComp`). The adjunction
`- ⊗ᴸ - ⊣₂ RHom(-, -)` is the tensor-hom adjunction of the monoidal closed category
`Dᵇc(X)⟦Λ⟧` (`boundedConstructibleTensorHomAdjunction₂`).

The exceptional inverse image `Rf^!` is not the restriction of a functor on the ambient derived
category: it is constructed on bounded constructible complexes directly, for the `ℓ`-adic
coefficient rings `E̲` and `ℚ̲̄_ℓ`, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek`.

## Sorried input

That the six functors preserve bounded constructible complexes is `sorry`ed:
`boundedConstructible_leftDerivedUpperStar_obj`, `boundedConstructible_rightDerivedLowerStar_obj`
and `boundedConstructible_openImmersionLowerShriek_obj`, and the instances
`isMonoidal_boundedConstructible` (`Dᵇc(X)⟦Λ⟧` contains `Λ_X` and is stable under `- ⊗ᴸ -`) and
`isMonoidalClosed_boundedConstructible` (`Dᵇc(X)⟦Λ⟧` is stable under `RHom(-, -)`).

These are theorems for the `ℓ`-adic coefficient rings, the condensed rings `E̲` of a finite
extension `E` of `ℚ_ℓ` and `ℚ̲̄_ℓ` (Deligne's finiteness theorems, Bhatt–Scholze, Section 6.8);
`Λ` is kept general here, the coefficient ring being an input of the statements.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- The bounded constructible derived category `D_cons(X_proét, Λ_X)` of module objects over
`Λ_X = p_X^* Λ`. -/
scoped notation "Dᵇc(" X ")⟦" Λ "⟧" =>
  AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj Λ X)

/-! ### The pullback and the pushforward -/

section UpperLowerStar

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The derived pullback `Lf^*` on module objects over `Λ` preserves bounded constructible
complexes. -/
lemma boundedConstructible_leftDerivedUpperStar_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left)))
    (hK : boundedConstructible (condensedRingObj Λ Y.left) K) :
    boundedConstructible (condensedRingObj Λ X.left) ((L((f.left)^*⟦Λ⟧)).obj K) :=
  sorry

/-- The derived pullback `Lf^* : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible complexes: the
restriction of `L((f)^*⟦Λ⟧)`. -/
noncomputable def boundedConstructibleUpperStar : Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((f.left)^*⟦Λ⟧))
    fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f K.obj K.property

/-- The restricted derived pullback is compatible with the inclusions. -/
noncomputable def boundedConstructibleUpperStarCompatibility :
    boundedConstructibleUpperStar Λ ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ L((f.left)^*⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` on bounded constructible complexes:
the restriction of `ProEtale.CondensedRing.leftDerivedUpperStarComp` along the fully
faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (g : Y ⟶ Z) :
    boundedConstructibleUpperStar Λ ℓ (f ≫ g) ≅
      boundedConstructibleUpperStar Λ ℓ g ⋙ boundedConstructibleUpperStar Λ ℓ f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (boundedConstructibleUpperStarCompatibility Λ ℓ (f ≫ g) ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp Λ f.left g.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility Λ ℓ g).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The derived pushforward `Rf_*` on module objects over `Λ` preserves bounded constructible
complexes. -/
lemma boundedConstructible_rightDerivedLowerStar_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hK : boundedConstructible (condensedRingObj Λ X.left) K) :
    boundedConstructible (condensedRingObj Λ Y.left) ((R((f.left)_*⟦Λ⟧)).obj K) :=
  sorry

/-- The derived pushforward `Rf_* : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded constructible complexes:
the restriction of `R((f)_*⟦Λ⟧)`. -/
noncomputable def boundedConstructibleLowerStar : Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(Y.left)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R((f.left)_*⟦Λ⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj Λ ℓ f K.obj K.property

/-- The restricted derived pushforward is compatible with the inclusions. -/
noncomputable def boundedConstructibleLowerStarCompatibility :
    boundedConstructibleLowerStar Λ ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f.left)_*⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes: the restriction of
`ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunction :
    boundedConstructibleUpperStar Λ ℓ f ⊣ boundedConstructibleLowerStar Λ ℓ f :=
  Adjunction.restrictFullyFaithful (derivedUpperStarLowerStarAdjunction Λ f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm
    (boundedConstructibleLowerStarCompatibility Λ ℓ f).symm

end UpperLowerStar

/-! ### The extension by zero along an open immersion -/

section OpenImmersion

include ℓ k

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The extension by zero `j_!` along an open immersion, applied levelwise to complexes of
module objects over `Λ`, preserves bounded constructible complexes. -/
lemma boundedConstructible_openImmersionLowerShriek_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
      (condensedRingObj Λ U.left)))
    (hK : boundedConstructible (condensedRingObj Λ U.left) K) :
    boundedConstructible (condensedRingObj Λ X.left) ((D((j.left)_!open⟦Λ⟧)).obj K) :=
  sorry

/-- The extension by zero `j_! : Dᵇc(U)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` along an open immersion on bounded
constructible complexes: the restriction of the levelwise functor `D((j)_!open⟦Λ⟧)`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriek : Dᵇc(U.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ D((j.left)_!open⟦Λ⟧))
    fun K ↦ boundedConstructible_openImmersionLowerShriek_obj Λ ℓ j K.obj K.property

/-- The restricted extension by zero is compatible with the inclusions. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekCompatibility :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ D((j.left)_!open⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `j_! ⊣ j^*` along an open immersion on bounded constructible complexes: the
restriction of `ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction`
along the fully faithful inclusions, the levelwise `D((j)^*⟦Λ⟧)` being identified with the
derived pullback `L((j)^*⟦Λ⟧)` that `boundedConstructibleUpperStar` restricts. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⊣ boundedConstructibleUpperStar Λ ℓ j :=
  Adjunction.restrictFullyFaithful
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j.left).symm)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).symm
    (boundedConstructibleUpperStarCompatibility Λ ℓ j).symm

end OpenImmersion

/-! ### The derived lower shriek -/

/-- The compactification of the underlying morphism of schemes `f.left` of a morphism `f` of
separated `k`-schemes of finite type chosen by Nagata's theorem
(`AlgebraicGeometry.HasCompactification.of_over`): the compactification
`HasCompactification.compactification f.left` for the instance it provides. It is the
compactification defining `boundedConstructibleLowerShriek`. -/
noncomputable abbrev compactificationOverField {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y) : Compactification f.left :=
  haveI := HasCompactification.of_over f
  HasCompactification.compactification f.left

section Shriek

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_* : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded
constructible complexes attached to a compactification `c = (X.left ⟶[i] Z ⟶[p] Y.left)` of
`f.left`: the extension by zero along the open immersion `i` followed by the derived pushforward
along the proper morphism `p`, both on bounded constructible complexes, for `i` and `p` the
morphisms `c.overI` and `c.overG` of `Over (Spec (.of k))`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactification :
    Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(Y.left)⟦Λ⟧ :=
  boundedConstructibleOpenImmersionLowerShriek Λ ℓ c.overI ⋙
    boundedConstructibleLowerStar Λ ℓ c.overG

/-- `Rf_!^c` on bounded constructible complexes is the restriction of the derived lower shriek
`Rf_!(c)⟦Λ⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationCompatibility :
    boundedConstructibleLowerShriekOfCompactification Λ ℓ c ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ Rf_!(c)⟦Λ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarCompatibility Λ ℓ c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ c.overI) _ ≪≫
    Functor.associator _ _ _

end OfCompactification

variable (f : X ⟶ Y)

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded constructible complexes:
the functor `boundedConstructibleLowerShriekOfCompactification` attached to the compactification
`compactificationOverField f` chosen by Nagata's theorem. -/
noncomputable def boundedConstructibleLowerShriek : Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(Y.left)⟦Λ⟧ :=
  boundedConstructibleLowerShriekOfCompactification Λ ℓ (compactificationOverField f)

lemma boundedConstructibleLowerShriek_eq :
    boundedConstructibleLowerShriek Λ ℓ f =
      boundedConstructibleLowerShriekOfCompactification Λ ℓ (compactificationOverField f) :=
  rfl

/-- The derived lower shriek on bounded constructible complexes is the restriction of the
derived lower shriek `R(f)_!⟦Λ⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekCompatibility :
    haveI := HasCompactification.of_over f
    boundedConstructibleLowerShriek Λ ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f.left)_!⟦Λ⟧ :=
  boundedConstructibleLowerShriekOfCompactificationCompatibility Λ ℓ
    (compactificationOverField f)

end Shriek


/-! ### The derived tensor product and the derived hom -/

section TensorHom

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- The bounded constructible complexes of module objects over `Λ` form a monoidal
subcategory of `D(Mod_{Λ_X})` for the derived tensor product: they contain the unit `Λ_X`
and are stable under `- ⊗ᴸ -`. -/
instance isMonoidal_boundedConstructible :
    (boundedConstructible (condensedRingObj Λ X.left)).IsMonoidal :=
  sorry

/-- The bounded constructible complexes of module objects over `Λ` are stable under the derived
hom `RHom(-, -)`, the internal hom of `D(Mod_{Λ_X})`. -/
instance isMonoidalClosed_boundedConstructible :
    (boundedConstructible (condensedRingObj Λ X.left)).IsMonoidalClosed :=
  sorry

/-- The derived tensor product `- ⊗ᴸ - : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded
constructible complexes: the tensor product of the monoidal structure on the full subcategory
`Dᵇc(X)⟦Λ⟧` (`ObjectProperty.fullMonoidalSubcategory`), the restriction of `-⊗ᴸ-(X)⟦Λ⟧` in
both variables. -/
noncomputable def boundedConstructibleTensor :
    Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  curriedTensor _

/-- The derived hom `RHom(-, -) : Dᵇc(X)⟦Λ⟧ᵒᵖ ⥤ Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible
complexes: the internal hom of the monoidal closed structure on the full subcategory
`Dᵇc(X)⟦Λ⟧` (`ObjectProperty.fullMonoidalClosedSubcategory`), the restriction of `RHom(X)⟦Λ⟧`
in both variables. -/
noncomputable def boundedConstructibleHom :
    (Dᵇc(X.left)⟦Λ⟧)ᵒᵖ ⥤ Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧ :=
  MonoidalClosed.internalHom

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦Λ⟧`, the restricted functor `K ⊗ᴸ -` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleTensorObjCompatibility (K : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleTensor Λ X).obj K ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (-⊗ᴸ-(X.left)⟦Λ⟧).obj K.obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleTensor, derivedTensor]

/-- For a fixed `K ∈ Dᵇc(X)⟦Λ⟧`, the restricted functor `RHom(K, -)` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleHomObjCompatibility (K : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleHom Λ X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (RHom(X.left)⟦Λ⟧).obj (op K.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

/-- The adjunction with a parameter `- ⊗ᴸ - ⊣₂ RHom(-, -)` on bounded constructible complexes:
the tensor-hom adjunction of the monoidal closed structure on `Dᵇc(X)⟦Λ⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction₂ :
    boundedConstructibleTensor Λ X ⊣₂ boundedConstructibleHom Λ X :=
  MonoidalClosed.internalHomAdjunction₂

/-- For a fixed `K ∈ Dᵇc(X)⟦Λ⟧`, the adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on bounded constructible
complexes: the tensor-hom adjunction `ihom.adjunction K` of the monoidal closed structure on
`Dᵇc(X)⟦Λ⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction (K : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleTensor Λ X).obj K ⊣ (boundedConstructibleHom Λ X).obj (op K) :=
  (boundedConstructibleTensorHomAdjunction₂ Λ).adj K

end TensorHom

end AlgebraicGeometry.ProEtale.CondensedRing
````

Source `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean`

Git blob: `f0901e75a60023242cc971f401a070ea4d413942`; SHA-256: `65e045ea9e75523cdb1daa00311fcb60aa6fa6c1e0277e6ceaca7d05bb9bef36`.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-!

# The bounded constructible `ℚ̄_ℓ`-complexes as the 2-colimit over the finite subextensions

Let `ℓ` be a prime and `X` a scheme. For a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
(`PadicAlgCl.FiniteIntermediateField ℓ`), let `C_E(X) = D^b_cons(X, E)` be the bounded
constructible derived category of modules over `E_X = p_X^* E̲`
(`ProEtale.BoundedConstructible (padicSubfieldRingObj X ℓ E)`, the full subcategory of the
unbounded `D(Mod_{E_X})` of `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`),
and let `C_Ω(X) = D^b_cons(X, ℚ̄_ℓ)` be the one of modules over `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ`. The
derived extensions of scalars
```
T^X_{E,F} = F_X ⊗ᴸ_{E_X} - ,   T^X_{E,Ω} = ℚ̄_ℓ,X ⊗ᴸ_{E_X} -
```
of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` are
*assumed* to preserve bounded constructibility
(`ProEtale.boundedConstructible_derivedExtendScalarsSubfield_obj`,
`ProEtale.boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj`), and hence restrict to
functors
```
ProEtale.constructibleExtendScalars h : C_E(X) ⥤ C_F(X)   (E ≤ F),
ProEtale.constructibleToPadicAlgCl E : C_E(X) ⥤ C_Ω(X),
```
compatible with each other through the transitivity of extension of scalars
(`ProEtale.constructibleToPadicAlgClCompIso`). Together these form a cocone of categories
`ProEtale.constructibleCocone X ℓ` on the directed system `E ↦ C_E(X)`, with vertex `C_Ω(X)`,
in the sense of `WeilConjectures.CategoryTheory.FilteredTwoColimit`.

The main statement, **`ℚ̄_ℓ` is a 2-colimit** (`ProEtale.constructibleCocone_isFilteredTwoColimit`),
is that this cocone is a filtered 2-colimit: the comparison functor
`2-colim_E C_E(X) ⟶ C_Ω(X)`, `(E, K_E) ↦ T^X_{E,Ω} K_E`, is an equivalence of ordinary
categories. By `CategoryTheory.CategoryCocone.IsFilteredTwoColimit` this is the conjunction of

* **(Obj)** `ProEtale.constructibleCocone_essSurjObj`: every bounded constructible
  `ℚ̄_ℓ,X`-complex `K` is isomorphic to `T^X_{E,Ω} K_E` for some finite subextension `E` and some
  bounded constructible `E_X`-complex `K_E` (descent of constructible objects);
* **(Hom)** `ProEtale.constructibleCocone_homSurj` and `ProEtale.constructibleCocone_homInj`:
  every morphism `T^X_{E,Ω} K_E ⟶ T^X_{F,Ω} L_F` in `D(Mod_{ℚ̄_ℓ,X})` is defined over some finite
  subextension `H ⊇ E, F`, and two morphisms over `H` with the same image are equal over some
  finite subextension `H' ⊇ H`. Since the bounded constructible complexes are stable under
  shifts, this includes the statement for the shifted targets `L_F[n]`, which is what the
  compatibility with the triangulated structures requires.

These are stated for a topologically noetherian `X`, the setting in which the bounded
constructible complexes form a triangulated subcategory
(`ProEtale.isTriangulated_boundedConstructible`). They are *not* formal consequences of the
identification `ℚ̄_ℓ,X ≃ colim_E E_X` of `ProEtale.isColimitPadicAlgClRingObjCocone`, and they
are false for the unbounded derived categories; see the module docstring of
`WeilConjectures.CategoryTheory.FilteredTwoColimit` for the ordinary-category model of the
2-colimit that they describe.

## Sorried input

* `ProEtale.boundedConstructible_derivedExtendScalarsSubfield_obj` and
  `ProEtale.boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj`: extension of scalars
  along `E_X ⟶ F_X` and `E_X ⟶ ℚ̄_ℓ,X` preserves bounded constructible complexes. The extension
  of scalars is exact
  (`ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap`), so it
  is computed termwise and preserves boundedness, and it sends a locally finitely
  presented module on a stratum to a locally finitely presented one, the presentation being
  tensored up.
* **(Obj)** `ProEtale.constructibleCocone_essSurjObj`: constructible descent. A bounded
  constructible `ℚ̄_ℓ,X`-complex has finitely many constructible cohomology sheaves; each is
  locally, on the strata of a stratification, finitely presented, and a finite presentation
  involves finitely many sections of `ℚ̄_ℓ,X`, which are defined over a finite subextension since
  `ℚ̄_ℓ,X = colim_E E_X` (`ProEtale.isColimitPadicAlgClRingObjCocone`). A finite Postnikov
  induction on the length of the complex then descends the complex itself, the gluing data being
  morphisms which descend by (Hom).
* **(Hom)** `ProEtale.constructibleCocone_homSurj` and `ProEtale.constructibleCocone_homInj`:
  continuity of the derived hom. For a bounded constructible first argument `K_E` and a
  bounded below second argument, `Hom_{D(Mod_{ℚ̄_ℓ,X})}(T_{E,Ω} K_E, T_{E,Ω} L_E)` is the filtered
  colimit over `H ⊇ E` of the `Hom_{D(Mod_{H_X})}(T_{E,H} K_E, T_{E,H} L_E)`: `K_E` is a finite
  extension of shifts of locally finitely presented modules, for which the derived hom into a
  filtered colimit of uniformly bounded below complexes is the filtered colimit of the derived
  homs, and `ℚ̄_ℓ,X = colim_H H_X`.

This is the input needed to transport base change theorems from finite to `ℚ̄_ℓ`-coefficients:
by (Obj) every constructible `K` is `T^X_{E,Ω} K_E`, and the compatibility of the base change
maps with the extension of scalars (built from the (Pull) and (Push) comparisons of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`) then shows that the
base change map at `K` is the extension of scalars of the one at `K_E`. This compatibility of
the base change maps of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems`
with the extension of scalars is not yet formalized.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Abelian

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The derived extensions of scalars and their transitivity -/

section ExtendScalars

/-- The derived extension of scalars `T^X_{E,F} = F_X ⊗ᴸ_{E_X} - : D(Mod_{E_X}) ⥤ D(Mod_{F_X})`
along the inclusion of finite subextensions `E ≤ F`. -/
noncomputable abbrev derivedExtendScalarsSubfield {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) :=
  L(Mod.extendScalars (padicSubfieldRingObjMap X ℓ h))

/-- The derived extension of scalars
`T^X_{E,Ω} = ℚ̄_ℓ,X ⊗ᴸ_{E_X} - : D(Mod_{E_X}) ⥤ D(Mod_{ℚ̄_ℓ,X})` along the inclusion of a finite
subextension `E` into `ℚ̄_ℓ`. -/
noncomputable abbrev derivedExtendScalarsToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ)) :=
  L(Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E))

/-- Transitivity of the derived extension of scalars: `T^X_{E,F} ⋙ T^X_{F,Ω} ≅ T^X_{E,Ω}` for
`E ≤ F`. The extensions of scalars being exact, the composite of their derived functors is the
derived functor of the composite, which is the extension of scalars along the composite
inclusion `E_X ⟶ F_X ⟶ ℚ̄_ℓ,X = E_X ⟶ ℚ̄_ℓ,X`. -/
noncomputable def derivedExtendScalarsCompIso {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsToPadicAlgCl X ℓ F ≅
      derivedExtendScalarsToPadicAlgCl X ℓ E :=
  haveI : PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h ≫
      padicSubfieldRingObjToPadicAlgCl X ℓ F)) :=
    preservesFiniteLimits_of_natIso
      (Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h)).symm
  (Functor.leftDerivedFunctorCompIso _ _).symm ≪≫
    Functor.leftDerivedFunctorNatIso _
      ((Mod.extendScalarsComp _ _).symm ≪≫
        Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h))

end ExtendScalars

/-! ### The bounded constructible categories and the functors between them -/

section Constructible

/-- The bounded constructible derived category `C_E(X) = D^b_cons(X, E)` of `E_X`-modules, for
a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
noncomputable abbrev PadicSubfieldConstructible (E : FiniteIntermediateField ℓ) : Type _ :=
  BoundedConstructible (padicSubfieldRingObj X ℓ E)

/-- The bounded constructible derived category `C_Ω(X) = D^b_cons(X, ℚ̄_ℓ)` of
`ℚ̄_ℓ,X`-modules. -/
noncomputable abbrev PadicAlgClConstructible : Type _ :=
  BoundedConstructible (padicAlgClRingObj X ℓ)

/-- Extension of scalars along `E_X ⟶ F_X` preserves bounded constructible complexes. See the
module docstring. -/
lemma boundedConstructible_derivedExtendScalarsSubfield_obj {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (hK : boundedConstructible (padicSubfieldRingObj X ℓ E) K) :
    boundedConstructible (padicSubfieldRingObj X ℓ F)
      ((derivedExtendScalarsSubfield X ℓ h).obj K) :=
  sorry

/-- Extension of scalars along `E_X ⟶ ℚ̄_ℓ,X` preserves bounded constructible complexes. See the
module docstring. -/
lemma boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj (E : FiniteIntermediateField ℓ)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (hK : boundedConstructible (padicSubfieldRingObj X ℓ E) K) :
    boundedConstructible (padicAlgClRingObj X ℓ) ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K) :=
  sorry

/-- The extension of scalars `T^X_{E,F} : C_E(X) ⥤ C_F(X)` on bounded constructible complexes,
for finite subextensions `E ≤ F`. -/
noncomputable def constructibleExtendScalars {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    PadicSubfieldConstructible X ℓ E ⥤ PadicSubfieldConstructible X ℓ F :=
  (boundedConstructible (padicSubfieldRingObj X ℓ F)).lift
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙ derivedExtendScalarsSubfield X ℓ h)
    (fun K ↦ boundedConstructible_derivedExtendScalarsSubfield_obj X ℓ h K.obj K.property)

/-- The extension of scalars `T^X_{E,Ω} : C_E(X) ⥤ C_Ω(X)` on bounded constructible complexes,
for a finite subextension `E`: the functors of the cocone whose vertex is the bounded
constructible `ℚ̄_ℓ`-complexes. -/
noncomputable def constructibleToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    PadicSubfieldConstructible X ℓ E ⥤ PadicAlgClConstructible X ℓ :=
  (boundedConstructible (padicAlgClRingObj X ℓ)).lift
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙ derivedExtendScalarsToPadicAlgCl X ℓ E)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj X ℓ E K.obj K.property)

/-- The functors to the bounded constructible `ℚ̄_ℓ`-complexes are compatible with the extensions
of scalars between finite subextensions: `T^X_{E,F} ⋙ T^X_{F,Ω} ≅ T^X_{E,Ω}` on bounded
constructible complexes, by `derivedExtendScalarsCompIso` and the full faithfulness of the
inclusion of the bounded constructible complexes. -/
noncomputable def constructibleToPadicAlgClCompIso {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    constructibleExtendScalars X ℓ h ⋙ constructibleToPadicAlgCl X ℓ F ≅
      constructibleToPadicAlgCl X ℓ E :=
  Functor.fullyFaithfulCancelRight (boundedConstructible (padicAlgClRingObj X ℓ)).ι
    ((Iso.refl ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
        (derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsToPadicAlgCl X ℓ F)) :
      (constructibleExtendScalars X ℓ h ⋙ constructibleToPadicAlgCl X ℓ F) ⋙
          (boundedConstructible (padicAlgClRingObj X ℓ)).ι ≅
        (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
          (derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsToPadicAlgCl X ℓ F)) ≪≫
      Functor.isoWhiskerLeft (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι
        (derivedExtendScalarsCompIso X ℓ h))

/-- The cocone of categories `E ↦ C_E(X)` with vertex `C_Ω(X)`: the directed system of the
bounded constructible `E`-complexes over the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, with the
extensions of scalars as transition functors, and the extensions of scalars to `ℚ̄_ℓ` as
functors to the vertex. -/
noncomputable def constructibleCocone :
    CategoryCocone (fun E : FiniteIntermediateField ℓ ↦ PadicSubfieldConstructible X ℓ E)
      (PadicAlgClConstructible X ℓ) where
  T h := constructibleExtendScalars X ℓ h
  Φ E := constructibleToPadicAlgCl X ℓ E
  iso h := constructibleToPadicAlgClCompIso X ℓ h

end Constructible

/-! ### `ℚ̄_ℓ` is a 2-colimit -/

section TwoColimit

variable [TopologicalSpace.NoetherianSpace X]

/-- **(Obj)**: every bounded constructible `ℚ̄_ℓ,X`-complex is isomorphic to the extension of
scalars `T^X_{E,Ω} K_E` of a bounded constructible `E_X`-complex `K_E` for some finite
subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. See the module docstring. -/
theorem constructibleCocone_essSurjObj : (constructibleCocone X ℓ).EssSurjObj :=
  sorry

/-- **(Hom), surjectivity**: every morphism `T^X_{E,Ω} K_E ⟶ T^X_{F,Ω} L_F` between extensions of
scalars of bounded constructible complexes is the extension of scalars of a morphism
`T^X_{E,H} K_E ⟶ T^X_{F,H} L_F` for some finite subextension `H ⊇ E, F`. See the module
docstring. -/
theorem constructibleCocone_homSurj : (constructibleCocone X ℓ).HomSurj :=
  sorry

/-- **(Hom), injectivity**: two morphisms of bounded constructible `H_X`-complexes with the same
extension of scalars to `ℚ̄_ℓ,X` have the same extension of scalars to `H'_X` for some finite
subextension `H' ⊇ H`. See the module docstring. -/
theorem constructibleCocone_homInj : (constructibleCocone X ℓ).HomInj :=
  sorry

/-- **`ℚ̄_ℓ` is a 2-colimit**: the bounded constructible derived category `D^b_cons(X, ℚ̄_ℓ)`
of `ℚ̄_ℓ,X`-modules, with the extensions of scalars from the bounded constructible derived
categories `D^b_cons(X, E)` of the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, is the filtered
2-colimit of the latter: the comparison functor `2-colim_E D^b_cons(X, E) ⟶ D^b_cons(X, ℚ̄_ℓ)`,
`(E, K_E) ↦ ℚ̄_ℓ,X ⊗ᴸ_{E_X} K_E`, is an equivalence of ordinary categories. -/
theorem constructibleCocone_isFilteredTwoColimit :
    (constructibleCocone X ℓ).IsFilteredTwoColimit where
  essSurjObj := constructibleCocone_essSurjObj X ℓ
  homSurj := constructibleCocone_homSurj X ℓ
  homInj := constructibleCocone_homInj X ℓ

end TwoColimit

end AlgebraicGeometry.ProEtale
````

Source `WeilConjectures/CategoryTheory/RingObjects/Condensed/EllAdic.lean`

Git blob: `229eca997d6f97a34f68105fbf628baf53a90340`; SHA-256: `9deccecc22e8a6364f8c63505b9bff1ea6ca74b87c235b64c7f18fda1fa1c70e`.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic

/-!

# The condensed coefficient rings `ℤ_ℓ`, `ℚ_ℓ`, `𝒪_E`, `E` and `ℚ̄_ℓ`

Fix a prime `ℓ`. The four *topological* `ℓ`-adic coefficient rings are defined as condensed
rings by their sections on profinite sets, following Section 3 of
`WeilConjectures/RefactorInstruction.tex`:
```
ℤ̲_ℓ(S) := C(S, ℤ_ℓ),   ℚ̲_ℓ(S) := C(S, ℚ_ℓ),   𝒪̲_E(S) := C(S, 𝒪_E),   E̲(S) := C(S, E),
```
with restriction by precomposition and the pointwise ring operations: each is
`Profinite.continuousMapRingSheaf` of the corresponding topological ring. Here `E` is a subfield
of `ℚ̄_ℓ = PadicAlgCl ℓ`, given by an embedding `E → ℚ̄_ℓ`, with the topology restricted from
`ℚ̄_ℓ` (`PadicAlgCl.normedFieldOfAlgebra`), and `𝒪_E = PadicAlgCl.integers ℓ E` is its ring of
integers.

The familiar descriptions `ℤ̲_ℓ ≅ lim_n ℤ/ℓⁿ`, `ℚ̲_ℓ ≅ ℤ̲_ℓ[1/ℓ]`, `𝒪̲_E ≅ lim_n 𝒪_E/ϖⁿ` and
`E̲ ≅ 𝒪̲_E[1/ϖ]` are *not* definitions; they are comparison isomorphisms, to be proved later.

The condensed `ℚ̄_ℓ` is not of the form `C(-, T)`. Following Definition 3.6 of the notes, a
section over a profinite set `S` is a continuous map `S → E` into a finite subextension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, regarded in `ℚ̄_ℓ`: the condensed ring `ℚ̲̄_ℓ` is the subsheaf of
`C(-, ℚ̄_ℓ)` of the maps with values in a finite subextension
(`Profinite.padicAlgClCondensedRing`). The sheaf condition is checked directly: a covering is
refined by a finite jointly surjective family, and finitely many finite subextensions have a
finite compositum. It is *not* `C(-, ℚ̄_ℓ)` for the valuation topology, which has more sections:
a sequence of elements of unbounded degree converging to `0` gives a continuous map on a
convergent sequence that takes values in no finite subextension.

The inclusions `ℤ_ℓ → ℚ_ℓ → E`, `ℤ_ℓ → 𝒪_E → E` are continuous ring homomorphisms, so
postcomposition with them gives morphisms of condensed rings.

## Main definitions

* `Profinite.padicIntCondensedRing`, `Profinite.padicCondensedRing`: the condensed rings
  `ℤ̲_ℓ` and `ℚ̲_ℓ`.
* `Profinite.padicSubfieldCondensedRing`, `Profinite.padicIntegersCondensedRing`: the condensed
  rings `E̲` and `𝒪̲_E`, and `Profinite.padicIntegersRingObj`: the ring object of condensed
  abelian groups underlying `𝒪̲_E`.
* `Profinite.padicIntCondensedRingToPadicCondensedRing`,
  `Profinite.padicCondensedRingToPadicSubfieldCondensedRing`,
  `Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing` and
  `Profinite.padicIntCondensedRingToPadicIntegersCondensedRing`: the inclusions, as morphisms of
  condensed rings.
* `Profinite.padicAlgClCondensedRing`: the condensed ring `ℚ̲̄_ℓ`, and
  `Profinite.padicAlgClRingObj`: the underlying ring object of condensed abelian groups.

-/

@[expose] public section

universe u

open CategoryTheory

namespace Profinite

open AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### `ℤ_ℓ` and `ℚ_ℓ` -/

/-- The condensed ring `ℤ̲_ℓ`, with sections `ℤ̲_ℓ(S) = C(S, ℤ_ℓ)` for the `ℓ`-adic topology. -/
noncomputable abbrev padicIntCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  continuousMapRingSheaf ℤ_[ℓ]

/-- The condensed ring `ℚ̲_ℓ`, with sections `ℚ̲_ℓ(S) = C(S, ℚ_ℓ)` for the `ℓ`-adic topology. -/
noncomputable abbrev padicCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  continuousMapRingSheaf ℚ_[ℓ]

/-- The inclusion `ℤ̲_ℓ ⟶ ℚ̲_ℓ`, a morphism of condensed rings. -/
noncomputable def padicIntCondensedRingToPadicCondensedRing :
    padicIntCondensedRing.{u} ℓ ⟶ padicCondensedRing ℓ :=
  continuousMapRingSheafMap PadicInt.Coe.ringHom continuous_subtype_val

/-! ### Subfields `E` of `ℚ̄_ℓ` -/

section Subfield

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The condensed ring `E̲`, for a subfield `E` of `ℚ̄_ℓ` given by an embedding `E → ℚ̄_ℓ`, with
sections `E̲(S) = C(S, E)` for the topology of `E` restricted from `ℚ̄_ℓ`. -/
noncomputable abbrev padicSubfieldCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheaf E

variable [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]

/-- The inclusion `ℚ̲_ℓ ⟶ E̲`, a morphism of condensed rings. -/
noncomputable def padicCondensedRingToPadicSubfieldCondensedRing :
    padicCondensedRing.{u} ℓ ⟶ padicSubfieldCondensedRing ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap (algebraMap ℚ_[ℓ] E) (continuous_algebraMap_padic_of_algebra ℓ E)

end Subfield

/-! ### The rings of integers `𝒪_E` -/

section Integers

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The condensed ring `𝒪̲_E`, for a subfield `E` of `ℚ̄_ℓ` given by an embedding `E → ℚ̄_ℓ`,
with sections `𝒪̲_E(S) = C(S, 𝒪_E)` into the ring of integers `𝒪_E = PadicAlgCl.integers ℓ E`,
for the topology restricted from `ℚ̄_ℓ`. -/
noncomputable abbrev padicIntegersCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheaf (PadicAlgCl.integers ℓ E)

/-- The inclusion `𝒪̲_E ⟶ E̲`, a morphism of condensed rings. -/
noncomputable def padicIntegersCondensedRingToPadicSubfieldCondensedRing :
    padicIntegersCondensedRing.{u} ℓ E ⟶ padicSubfieldCondensedRing ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap (PadicAlgCl.integers ℓ E).subtype continuous_subtype_val

/-- The condensed ring `𝒪̲_E` as a ring object of condensed abelian groups: the abelian sheaf
underlying `padicIntegersCondensedRing ℓ E`, with the ring object structure
`CategoryTheory.Sheaf.monObj_sheafCompose_obj`. -/
noncomputable abbrev padicIntegersRingObj : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (padicIntegersCondensedRing ℓ E)

/-- The condensed ring `𝒪̲_E` is a commutative ring object of condensed abelian groups. -/
instance isCommMonObj_padicIntegersRingObj : IsCommMonObj (padicIntegersRingObj.{u} ℓ E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  isCommMonObj_continuousMapRingObj (PadicAlgCl.integers ℓ E)

variable [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]

/-- The inclusion `ℤ̲_ℓ ⟶ 𝒪̲_E`, a morphism of condensed rings. -/
noncomputable def padicIntCondensedRingToPadicIntegersCondensedRing :
    padicIntCondensedRing.{u} ℓ ⟶ padicIntegersCondensedRing ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap (padicIntToIntegers ℓ E) (continuous_padicIntToIntegers ℓ E)

end Integers

/-! ### `ℚ̄_ℓ` -/

section PadicAlgCl

/-- The subfunctor of `S ↦ C(S, ℚ̄_ℓ)` on profinite sets of the continuous maps with values in a
finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`: a section is a continuous map into one finite local
field `E`, regarded in `ℚ̄_ℓ`. -/
def padicAlgClSubfunctor :
    Subfunctor (ContinuousMap.yonedaPresheaf Profinite.toTopCat.{u} (PadicAlgCl ℓ)) where
  obj S := {a | a ∈ PadicAlgCl.finiteIntermediateFieldValued ℓ S.unop}
  map {S S'} u a ha := by
    obtain ⟨E, hE, h⟩ := ha
    exact ⟨E, hE, fun x ↦ h _⟩

/-- The sections with values in a finite subextension form a sheaf for the coherent topology:
a covering is refined by a finite jointly surjective family `{Sᵢ ⟶ S}`, and if `a ∘ πᵢ` takes
values in the finite subextension `Eᵢ` for each `i`, then `a` takes values in their compositum,
which is again finite. -/
lemma isSheaf_padicAlgClSubfunctor :
    Presieve.IsSheaf (coherentTopology Profinite.{u}) (padicAlgClSubfunctor.{u} ℓ).toFunctor := by
  rw [Subfunctor.isSheaf_iff _
    (h := (isSheaf_iff_isSheaf_of_type _ _).mp (isSheaf_yonedaPresheaf (PadicAlgCl ℓ)))]
  intro S a ha
  obtain ⟨α, _, Y, π, hπ, hmem⟩ := (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily _).mp ha
  choose E hE h using hmem
  have hsurj : ∀ b : S.unop, ∃ (i : α) (y : Y i), π i y = b :=
    ((Profinite.effectiveEpiFamily_tfae Y π).out 0 2).mp hπ
  refine ⟨⨆ i, E i, inferInstance, fun x ↦ ?_⟩
  obtain ⟨i, y, rfl⟩ := hsurj x
  exact (le_iSup E i) (h i y)

/-- The presheaf of rings `S ↦ {a ∈ C(S, ℚ̄_ℓ) | a takes values in a finite subextension}` on
profinite sets, lifted to `Type (u + 1)`. -/
noncomputable def padicAlgClRingPresheaf : Profinite.{u}ᵒᵖ ⥤ RingCat.{u + 1} where
  obj S := RingCat.of (ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ S.unop))
  map u := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((((ContinuousMap.compRightAlgHom ℤ (PadicAlgCl ℓ) u.unop.hom.hom).toRingHom).comp
          (PadicAlgCl.finiteIntermediateFieldValued ℓ _).subtype).codRestrict
          (PadicAlgCl.finiteIntermediateFieldValued ℓ _) (fun a ↦ by
            obtain ⟨E, hE, h⟩ := a.2
            exact ⟨E, hE, fun x ↦ h _⟩)).comp ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The presheaf of types underlying `padicAlgClRingPresheaf ℓ` is the subfunctor
`padicAlgClSubfunctor ℓ`, lifted by one universe. -/
noncomputable def padicAlgClRingPresheafForgetIso :
    padicAlgClRingPresheaf.{u} ℓ ⋙ forget RingCat.{u + 1} ≅
      (padicAlgClSubfunctor.{u} ℓ).toFunctor ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The presheaf of rings of sections with values in a finite subextension is a sheaf. -/
lemma isSheaf_padicAlgClRingPresheaf :
    Presheaf.IsSheaf (coherentTopology Profinite.{u}) (padicAlgClRingPresheaf ℓ) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget RingCat.{u + 1}),
    Presheaf.isSheaf_of_iso_iff (padicAlgClRingPresheafForgetIso ℓ),
    isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff]
  exact isSheaf_padicAlgClSubfunctor ℓ

/-- The condensed ring `ℚ̲̄_ℓ`, following Definition 3.6 of
`WeilConjectures/RefactorInstruction.tex`: a section over a profinite set `S` is a continuous map
`S → E` into a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, regarded in `ℚ̄_ℓ`, so that two such
maps are identified when they agree pointwise in `ℚ̄_ℓ`. Restriction is precomposition and the
ring operations are computed in a common finite subextension. It is *not* `C(-, ℚ̄_ℓ)` for the
valuation topology of `ℚ̄_ℓ`, which has more sections. -/
noncomputable def padicAlgClCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  ⟨padicAlgClRingPresheaf ℓ, isSheaf_padicAlgClRingPresheaf ℓ⟩

/-- The condensed ring `ℚ̲̄_ℓ` as a ring object of condensed abelian groups: the abelian sheaf
underlying `padicAlgClCondensedRing ℓ`, with the ring object structure
`CategoryTheory.Sheaf.monObj_sheafCompose_obj`. -/
noncomputable abbrev padicAlgClRingObj : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (padicAlgClCondensedRing ℓ)

/-- The condensed ring `ℚ̲̄_ℓ` is a commutative ring object of condensed abelian groups. -/
instance isCommMonObj_padicAlgClRingObj : IsCommMonObj (padicAlgClRingObj.{u} ℓ) :=
  Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (padicAlgClCondensedRing ℓ) fun S
      (a b : ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ S.unop)) ↦ mul_comm a b

end PadicAlgCl

end Profinite
````

Source `WeilConjectures/CategoryTheory/ModuleObjects/Free.lean`

Git blob: `b703bc949aa37f19272db8256d0b5c7d323b78b3`; SHA-256: `0a619e2a337d10d7944faef26d800036272cafd9cda3ec0376fbec45fcc8c8f3`.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian

/-!

# Free and finitely presented module objects

Let `C` be an abelian monoidal category whose tensor product is additive in each variable, and
`R : C` an algebra object such that `R ⊗ -` is right exact, so that `Mod C R` is abelian.

* `Mod.free R n` is the free module `R^n = R ⊕ ⋯ ⊕ R` of rank `n`.
* `Mod.IsFree R M`: `M` is isomorphic to `R^n` for some `n`.
* `Mod.IsFinitelyPresented R M`: `M` is isomorphic to the cokernel of a morphism
  `R^m ⟶ R^n` between free modules of finite rank.
* `Mod.freeFunctor R : C ⥤ Mod C R` is the free module functor `M ↦ R ⊗ M`, for any monoid
  object `R` of a monoidal category.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

section Abelian

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  (R : C) [MonObj R] [PreservesFiniteColimits (tensorLeft R)]

/-- The free module object of rank `n`. -/
noncomputable abbrev free (n : ℕ) : Mod C R :=
  ⨁ fun _ : Fin n ↦ regular R

/-- A module object is *locally free of rank `n`* in the trivial (global) sense if it is
isomorphic to `R^n`; see the geometric files for the local version. -/
def IsFree (M : Mod C R) : Prop :=
  ∃ n : ℕ, Nonempty (M ≅ free R n)

/-- A module object is *finitely presented* if it is isomorphic to the cokernel of a morphism
`R^m ⟶ R^n` between free modules of finite rank. -/
def IsFinitelyPresented (M : Mod C R) : Prop :=
  ∃ (n m : ℕ) (f : free R m ⟶ free R n), Nonempty (M ≅ cokernel f)

end Abelian

section FreeFunctor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (R : C) [MonObj R]

open MonObj

/-- The free module object structure on `R ⊗ M`: `R` acts on the left factor through its
multiplication. -/
@[instance_reducible]
def freeModObj (M : C) : ModObj R (R ⊗ M) where
  smul := (α_ R R M).inv ≫ μ ▷ M
  one_smul := by
    change η ▷ (R ⊗ M) ≫ (α_ R R M).inv ≫ μ ▷ M = (λ_ (R ⊗ M)).hom
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, MonObj.one_mul]
    simp
  mul_smul := by
    change μ ▷ (R ⊗ M) ≫ (α_ R R M).inv ≫ μ ▷ M =
      (α_ R R (R ⊗ M)).hom ≫ R ◁ ((α_ R R M).inv ≫ μ ▷ M) ≫ (α_ R R M).inv ≫ μ ▷ M
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, MonObj.mul_assoc]
    simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [associator_inv_naturality_middle_assoc]
    monoidal

/-- The free module object functor `M ↦ R ⊗ M`, left adjoint to the forgetful functor. -/
@[simps]
def freeFunctor : C ⥤ Mod C R where
  obj M := { X := R ⊗ M, mod := freeModObj R M }
  map {M N} f :=
    letI := freeModObj R M
    letI := freeModObj R N
    { hom := R ◁ f
      isModHom := ⟨by
        change ((α_ R R M).inv ≫ μ ▷ M) ≫ R ◁ f = R ◁ (R ◁ f) ≫ (α_ R R N).inv ≫ μ ▷ N
        rw [Category.assoc, ← whisker_exchange, associator_inv_naturality_right_assoc]⟩ }

end FreeFunctor

end CategoryTheory.Mod
````

Source `WeilConjectures/TateTwist/RootsOfUnity.lean`

Git blob: `0f5b6637bf1dbffbc7b5369194341d9cfc1b7871`; SHA-256: `b774d9b3106104333bd6cffe54461f35eb5ee03ff755db1dc7eb3c3f538a51a9`.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic

/-!

# The sheaves of roots of unity on the pro-étale site

Let `X` be a scheme and `n` a natural number. The sheaf `μ_n` of `n`-th roots of unity on the
small pro-étale site `X_proét` is the sheafification of the abelian presheaf
```
U ↦ μ_n(Γ(U, 𝒪_U)) = {x ∈ Γ(U, 𝒪_U)ˣ | xⁿ = 1},
```
written additively and lifted to the universe `u + 1` of the coefficient sheaves of
`WeilConjectures.CategoryTheory.RingObjects.EllAdic`. (The presheaf is already an fpqc sheaf,
`μ_n` being representable, but this is not needed: the sheafification is canonically
isomorphic to it.)

For a prime `ℓ`, the `ℓ`-th power maps `μ_{ℓ^{n+1}} ⟶ μ_{ℓ^n}` form the inverse system whose
limit is the Tate module `ℤ_ℓ(1)`, see `WeilConjectures.TateTwist.ProEtale`.

## Main definitions

- `CommRingCat.rootsOfUnityFunctor n`: the functor `R ↦ μ_n(R)` from commutative rings to
  abelian groups, and `CommRingCat.rootsOfUnityPow n m`: the `m`-th power map
  `μ_{m n}(R) ⟶ μ_n(R)`, natural in `R`.
- `AlgebraicGeometry.ProEtale.rootsOfUnityPresheaf X n`: the presheaf `U ↦ μ_n(Γ(U, 𝒪_U))` on
  `X_proét`, and `AlgebraicGeometry.ProEtale.rootsOfUnitySheaf X n`: its sheafification `μ_n`.
- `AlgebraicGeometry.ProEtale.rootsOfUnitySheafPow X n m`: the `m`-th power map
  `μ_{m n} ⟶ μ_n`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CommRingCat

variable (n : ℕ)

/-- The functor `R ↦ μ_n(R)` sending a commutative ring to its group of `n`-th roots of unity,
written additively and lifted to the universe `u + 1`. -/
noncomputable def rootsOfUnityFunctor : CommRingCat.{u} ⥤ Ab.{u + 1} where
  obj R := AddCommGrpCat.of (ULift.{u + 1} (Additive (rootsOfUnity n R)))
  map f := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((restrictRootsOfUnity f.hom n).toAdditive.comp AddEquiv.ulift.toAddMonoidHom))
  map_id _ := by
    ext
    rfl
  map_comp _ _ := by
    ext
    rfl

lemma rootsOfUnityFunctor_map_apply_val {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : (rootsOfUnityFunctor n).obj R) :
    (((rootsOfUnityFunctor n).map f x).down.toMul : Sˣ).val =
      f.hom (x.down.toMul : Rˣ).val :=
  rfl

/-- The `m`-th power map `μ_{m n}(R) ⟶ μ_n(R)`, as a monoid homomorphism. -/
def rootsOfUnityPowHom (m : ℕ) (R : Type*) [CommMonoid R] :
    rootsOfUnity (m * n) R →* rootsOfUnity n R where
  toFun x := ⟨x.1 ^ m, (mem_rootsOfUnity _ _).2 (by
    rw [← pow_mul]
    exact (mem_rootsOfUnity _ _).1 x.2)⟩
  map_one' := Subtype.ext (one_pow m)
  map_mul' x y := Subtype.ext (mul_pow x.1 y.1 m)

/-- The `m`-th power map `μ_{m n} ⟶ μ_n`, natural in the commutative ring. -/
noncomputable def rootsOfUnityPow (m : ℕ) :
    rootsOfUnityFunctor.{u} (m * n) ⟶ rootsOfUnityFunctor.{u} n where
  app R := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((rootsOfUnityPowHom n m R).toAdditive.comp AddEquiv.ulift.toAddMonoidHom))
  naturality _ _ f := by
    ext x
    apply ULift.ext
    apply Subtype.ext
    apply Units.ext
    exact (map_pow f.hom _ m).symm

end CommRingCat

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (n : ℕ)

/-- The presheaf `U ↦ μ_n(Γ(U, 𝒪_U))` of `n`-th roots of unity on the small pro-étale site of
`X`, written additively and lifted to the universe `u + 1`. -/
noncomputable def rootsOfUnityPresheaf : X.ProEtᵒᵖ ⥤ Ab.{u + 1} :=
  (ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ ⋙ CommRingCat.rootsOfUnityFunctor n

/-- The sheaf `μ_n` of `n`-th roots of unity on the small pro-étale site of `X`: the
sheafification of `U ↦ μ_n(Γ(U, 𝒪_U))`. -/
noncomputable def rootsOfUnitySheaf : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  (presheafToSheaf (ProEt.topology X) Ab.{u + 1}).obj (rootsOfUnityPresheaf X n)

/-- The `m`-th power map `μ_{m n} ⟶ μ_n` of sheaves of roots of unity on `X_proét`. -/
noncomputable def rootsOfUnitySheafPow (m : ℕ) :
    rootsOfUnitySheaf X (m * n) ⟶ rootsOfUnitySheaf X n :=
  (presheafToSheaf (ProEt.topology X) Ab.{u + 1}).map
    (Functor.whiskerLeft ((ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ)
      (CommRingCat.rootsOfUnityPow n m))

end AlgebraicGeometry.ProEtale
````

Source `WeilConjectures/SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean`

Git blob: `7fee1fe3d0a1bb70fae3fe4462bdf1fd32c96d32`; SHA-256: `18ba53d27bb8a6aa93ca04a8462110f12637384160c36a6c3bc134d0ed78a05c`.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek

/-!

# Compatibility of the six functors with a change of condensed coefficient rings

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, i.e. of commutative ring objects
of abelian sheaves on `*_proét`. For a scheme `X`, its pullback along `p_X` is a morphism of ring
objects `a_X : Λ_X ⟶ Λ'_X` (`ProEtale.coefficientMap`), inducing the *derived extension of
scalars*
```
T^X = Λ'_X ⊗ᴸ_{Λ_X} - = L(Ext_{a_X}) : D(Mod_{Λ_X}) ⥤ D(Mod_{Λ'_X}).
```
This file constructs the *canonical comparison transformations* between these and the derived
functors `Lf^*`, `Rf_*`, `Rf_!` on module objects of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject`, for a morphism of schemes `f : X ⟶ Y`.
Following Corollary `cor:coeff-functor` of `WeilConjectures/RefactorInstruction.tex`, the
coefficient changes `a_X` are compatible with the canonical coefficient morphisms: the squares
```
  f^* Λ_Y --f^* a_Y--> f^* Λ'_Y              Λ_Y ----a_Y----> Λ'_Y
     |                     |                   |                |
    α_f                   α_f                 η_f              η_f
     ↓                     ↓                   ↓                ↓
    Λ_X -------a_X------> Λ'_X              f_* Λ_X --f_* a_X--> f_* Λ'_X
```
commute (`ProEtale.map_coefficientMap_comp_condensedPullbackHom`,
`ProEtale.condensedPushforwardHom_comp_map_coefficientMap`): the first is the naturality in `Λ`
of the comparison `f^* ∘ p_Y^* ≅ p_X^*`, and the second follows by adjunction. From these
squares, by the mate and conjugate constructions of
`WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`:

* **restriction of scalars commutes with the pushforward**, strictly
  (`ProEtale.CondensedRing.comapLowerStarIso`): both composites are `mapMod(f_*)` followed by
  the restriction of scalars along the common composite of the square; and in the derived
  categories (`ProEtale.CondensedRing.derivedComapLowerStarIso`), when `Λ'_X` is flat over
  `Λ_X`, so that the restriction of scalars preserves K-injective complexes;
* **(Pull)** `Lf^*_Λ ⋙ T^X ≅ T^Y ⋙ Lf^*_Λ'` (`ProEtale.CondensedRing.derivedPullIso`, and the
  underived `ProEtale.CondensedRing.pullIso`): the *conjugates* of the previous isomorphisms
  along `Lf^* ⊣ Rf_*` and `L(Ext) ⊣ D(Res)`, hence isomorphisms on all unbounded objects;
* **(Push)** `Rf_*^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_*^Λ'` (`ProEtale.CondensedRing.derivedPushHom`, and the
  underived `ProEtale.CondensedRing.pushHom`): the *mates* of the previous isomorphisms. They
  are not isomorphisms in general;
* **restriction of scalars commutes with the pullback**
  (`ProEtale.CondensedRing.comapUpperStarIso`), since every `α_f` is an isomorphism, and with
  the extension by zero along an open immersion `j`
  (`ProEtale.CondensedRing.comapOpenImmersionLowerShriekIso`). Hence the comparison
  `j_!^Λ ⋙ T^X ≅ T^U ⋙ j_!^Λ'` is an *isomorphism*, being the conjugate of the former along
  `j_! ⊣ j^*` (`ProEtale.CondensedRing.openImmersionShriekIso`, and its derived version
  `ProEtale.CondensedRing.derivedOpenImmersionShriekIso`);
* **(Shriek)** `Rf_!^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_!^Λ'`
  (`ProEtale.CondensedRing.derivedLowerShriekHom`), for `Rf_! = Di_! ⋙ Rg_*` attached to the
  chosen compactification `X ⟶[i] Z ⟶[g] Y` of `f`: the derived (Push) for the proper `g`
  followed by the derived (Shriek) isomorphism for the open immersion `i`. It is an
  isomorphism whenever (Push) is one for `g`
  (`ProEtale.CondensedRing.isIso_derivedLowerShriekHom`).

The compatibilities with the derived tensor product, the derived hom and `Rf^!` are not
treated: they require the strong monoidality of the extension of scalars, respectively
perfectness or duality hypotheses, which are not formalized.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Abelian

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### The coefficient changes `a_X` and the coefficient morphisms -/

section CoefficientMap

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [MonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

/-- The coefficient change `a_X = p_X^* a : Λ_X ⟶ Λ'_X` on `X_proét` induced by a morphism
`a : Λ ⟶ Λ'` of condensed rings. It is a morphism of ring objects, `p_X^*` being monoidal. -/
noncomputable abbrev coefficientMap (X : Scheme.{u}) :
    condensedRingObj Λ X ⟶ condensedRingObj Λ' X :=
  (upperStarFromPoint X).map a

omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
lemma coefficientMap_id (X : Scheme.{u}) : coefficientMap (𝟙 Λ) X = 𝟙 _ :=
  (upperStarFromPoint X).map_id Λ

omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
lemma coefficientMap_comp {Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    (b : Λ' ⟶ Λ'') (X : Scheme.{u}) :
    coefficientMap (a ≫ b) X = coefficientMap a X ≫ coefficientMap b X :=
  (upperStarFromPoint X).map_comp a b

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
/-- The coefficient morphisms `α_f : f^* Λ_Y ⟶ Λ_X` are natural in the condensed ring:
`f^* a_Y ≫ α_f = α_f ≫ a_X`. This is the naturality in `Λ` of the comparison
`f^* ∘ p_Y^* ≅ p_X^*`. -/
@[reassoc]
lemma map_coefficientMap_comp_condensedPullbackHom :
    (f)^*[Ab.{u + 1}].map (coefficientMap a Y) ≫ condensedPullbackHom Λ' f =
      condensedPullbackHom Λ f ≫ coefficientMap a X :=
  (upperStarFromPointComp f).hom.naturality a

omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in
/-- The coefficient morphisms `η_f : Λ_Y ⟶ f_* Λ_X` are natural in the condensed ring:
`η_f ≫ f_* a_X = a_Y ≫ η_f`. This follows from the naturality of `α_f` and of the unit of
`f^* ⊣ f_*`. -/
@[reassoc]
lemma condensedPushforwardHom_comp_map_coefficientMap :
    condensedPushforwardHom Λ f ≫ (f)_*[Ab.{u + 1}].map (coefficientMap a X) =
      coefficientMap a Y ≫ condensedPushforwardHom Λ' f := by
  rw [← unitAlgHom_comp_map_condensedPullbackHom, ← unitAlgHom_comp_map_condensedPullbackHom,
    Category.assoc, ← Functor.map_comp, ← map_coefficientMap_comp_condensedPullbackHom,
    Functor.map_comp]
  exact ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.naturality_assoc _ _).symm

end CoefficientMap

namespace CondensedRing

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-! ### Pushforward and pullback -/

section UpperLowerStar

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Restriction of scalars commutes with the pushforward:
`f_*^Λ' ⋙ Res_{a_Y} ≅ Res_{a_X} ⋙ f_*^Λ`, both being `mapMod(f_*)` followed by the restriction
of scalars along the common composite of the square `a_Y ≫ η_f = η_f ≫ f_* a_X`. -/
noncomputable def comapLowerStarIso :
    (f)_*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a Y) ≅ Mod.comap (coefficientMap a X) ⋙ (f)_*⟦Λ⟧ :=
  Mod.comapMapModComapIso (f)_*[Ab.{u + 1}] (coefficientMap a X) (coefficientMap a Y)
    (condensedPushforwardHom Λ f) (condensedPushforwardHom Λ' f)
    (condensedPushforwardHom_comp_map_coefficientMap a f).symm

/-- **(Pull)**, underived: `f^*_Λ ⋙ Ext_{a_X} ≅ Ext_{a_Y} ⋙ f^*_Λ'`, the conjugate of
`comapLowerStarIso` along `f^* ⊣ f_*` and `Ext ⊣ Res`. -/
noncomputable def pullIso :
    (f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X) ≅
      Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧ :=
  Adjunction.pullIsoOfComapIso (Mod.extendRestrictAdjunction (coefficientMap a X))
    (Mod.extendRestrictAdjunction (coefficientMap a Y))
    (upperStarLowerStarAdjunction Λ f) (upperStarLowerStarAdjunction Λ' f)
    (comapLowerStarIso a f)

/-- **(Push)**, underived: the canonical comparison `f_*^Λ ⋙ Ext_{a_Y} ⟶ Ext_{a_X} ⋙ f_*^Λ'`,
the mate of `comapLowerStarIso` along `Ext ⊣ Res`. -/
noncomputable def pushHom :
    (f)_*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a Y) ⟶
      Mod.extendScalars (coefficientMap a X) ⋙ (f)_*⟦Λ'⟧ :=
  Adjunction.pushHomOfComapIso (Mod.extendRestrictAdjunction (coefficientMap a X))
    (Mod.extendRestrictAdjunction (coefficientMap a Y)) (comapLowerStarIso a f)

/-- For every `f`, restriction of scalars commutes with the pullback:
`f^*_Λ' ⋙ Res_{a_X} ≅ Res_{a_Y} ⋙ f^*_Λ`, since the coefficient morphisms `α_f` are
isomorphisms. -/
noncomputable def comapUpperStarIso :
    (f)^*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a X) ≅ Mod.comap (coefficientMap a Y) ⋙ (f)^*⟦Λ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((f)^*[Ab.{u + 1}].mapMod (R := condensedRingObj Λ' Y))
      (Mod.extendScalarsComapIsoOfIsIso ((f)^*[Ab.{u + 1}].map (coefficientMap a Y))
        (coefficientMap a X) (condensedPullbackHom Λ f) (condensedPullbackHom Λ' f)
        (map_coefficientMap_comp_condensedPullbackHom a f).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((f)^*[Ab.{u + 1}].mapModComapIso (coefficientMap a Y)).symm
      (Mod.extendScalars (condensedPullbackHom Λ f)) ≪≫
    Functor.associator _ _ _

/-- Restriction of scalars commutes with the levelwise derived pullback:
`Df^*_Λ' ⋙ D(Res_{a_X}) ≅ D(Res_{a_Y}) ⋙ Df^*_Λ`. -/
noncomputable def derivedComapUpperStarIso :
    D((f)^*⟦Λ'⟧) ⋙ D(Mod.comap (coefficientMap a X)) ≅
      D(Mod.comap (coefficientMap a Y)) ⋙ D((f)^*⟦Λ⟧) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (comapUpperStarIso a f) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

end UpperLowerStar

/-! ### Derived pushforward and pullback, for a flat coefficient change -/

section Derived

variable [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]

instance preservesHomology_extendScalars_coefficientMap (X : Scheme.{u}) :
    (Mod.extendScalars (coefficientMap a X)).PreservesHomology := {}

/-- The restriction of scalars along a flat coefficient change `a_X : Λ_X ⟶ Λ'_X` preserves
K-injective complexes, its left adjoint being exact. -/
instance preservesKInjectiveComplexes_comap_coefficientMap (X : Scheme.{u}) :
    (Mod.comap (coefficientMap a X) :
      Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X) ⥤
        Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
      ).PreservesKInjectiveComplexes :=
  (Mod.extendRestrictAdjunction (coefficientMap a X)).preservesKInjectiveComplexes

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Restriction of scalars commutes with the derived pushforward:
`Rf_*^Λ' ⋙ D(Res_{a_Y}) ≅ D(Res_{a_X}) ⋙ Rf_*^Λ`. The restriction of scalars is exact and, `Λ'_X`
being flat over `Λ_X`, preserves K-injective complexes, so both sides are the right derived
functor of the two equal composites of `comapLowerStarIso`. -/
noncomputable def derivedComapLowerStarIso :
    R((f)_*⟦Λ'⟧) ⋙ D(Mod.comap (coefficientMap a Y)) ≅
      D(Mod.comap (coefficientMap a X)) ⋙ R((f)_*⟦Λ⟧) :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso (f)_*⟦Λ'⟧
      (Mod.comap (coefficientMap a Y))).symm ≪≫
    Functor.rightDerivedFunctorNatIso (comapLowerStarIso a f) ≪≫
    Functor.rightDerivedFunctorCompIso (Mod.comap (coefficientMap a X)) (f)_*⟦Λ⟧ ≪≫
    Functor.isoWhiskerRight
      (Mod.comap (coefficientMap a X)).rightDerivedFunctorIsoMapDerivedCategory R((f)_*⟦Λ⟧)

/-- **(Pull)**: `Lf^*_Λ ⋙ T^X ≅ T^Y ⋙ Lf^*_Λ'`, the conjugate of `derivedComapLowerStarIso` along
the derived adjunctions. It is an isomorphism on all unbounded objects. -/
noncomputable def derivedPullIso :
    L((f)^*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a X)) ≅
      L(Mod.extendScalars (coefficientMap a Y)) ⋙ L((f)^*⟦Λ'⟧) :=
  Adjunction.pullIsoOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (derivedUpperStarLowerStarAdjunction Λ f) (derivedUpperStarLowerStarAdjunction Λ' f)
    (derivedComapLowerStarIso a f)

/-- **(Push)**: the canonical comparison `Rf_*^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_*^Λ'`, the mate of
`derivedComapLowerStarIso` along `L(Ext) ⊣ D(Res)`. It is not an isomorphism in general. -/
noncomputable def derivedPushHom :
    R((f)_*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a Y)) ⟶
      L(Mod.extendScalars (coefficientMap a X)) ⋙ R((f)_*⟦Λ'⟧) :=
  Adjunction.pushHomOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (derivedComapLowerStarIso a f)

end Derived

/-! ### Extension by zero along an open immersion -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Restriction of scalars commutes with the extension by zero along an open immersion:
`j_!^Λ' ⋙ Res_{a_X} ≅ Res_{a_U} ⋙ j_!^Λ`, by the naturality of the projection formula and the
square of the coefficient morphisms `α_j`. -/
noncomputable def comapOpenImmersionLowerShriekIso :
    (j)_!open⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a X) ≅
      Mod.comap (coefficientMap a U) ⋙ (j)_!open⟦Λ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Mod.comap (condensedPullbackHom Λ' j))
      ((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1}
        j).projectionFormula.mapModLeftComapIso (coefficientMap a X)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Mod.comapComp _ _).symm ≪≫
      Mod.comapIsoOfEq (map_coefficientMap_comp_condensedPullbackHom a j) ≪≫
      Mod.comapComp _ _) _ ≪≫
    Functor.associator _ _ _

/-- **(Shriek) for an open immersion**, underived: `j_!^Λ ⋙ Ext_{a_X} ≅ Ext_{a_U} ⋙ j_!^Λ'`, the
conjugate of `comapUpperStarIso` along `j_! ⊣ j^*` and `Ext ⊣ Res`. -/
noncomputable def openImmersionShriekIso :
    (j)_!open⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X) ≅
      Mod.extendScalars (coefficientMap a U) ⋙ (j)_!open⟦Λ'⟧ :=
  (conjugateIsoEquiv ((Mod.extendRestrictAdjunction (coefficientMap a U)).comp
    (openImmersionLowerShriekUpperStarAdjunction Λ' j))
    ((openImmersionLowerShriekUpperStarAdjunction Λ j).comp
      (Mod.extendRestrictAdjunction (coefficientMap a X)))).symm
    (comapUpperStarIso a j)

/-- **(Shriek) for an open immersion**: `Dj_!^Λ ⋙ T^X ≅ T^U ⋙ Dj_!^Λ'`, the conjugate of
`derivedComapUpperStarIso` along the derived adjunctions `Dj_! ⊣ Dj^*` and
`L(Ext) ⊣ D(Res)`. It is an isomorphism on all unbounded objects. -/
noncomputable def derivedOpenImmersionShriekIso :
    D((j)_!open⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a X)) ≅
      L(Mod.extendScalars (coefficientMap a U)) ⋙ D((j)_!open⟦Λ'⟧) :=
  (conjugateIsoEquiv
    ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U)).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j))
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)))).symm
    (derivedComapUpperStarIso a j)

end OpenImmersion

/-! ### Derived lower shriek -/

section LowerShriek

variable [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- **(Shriek)**: the canonical comparison `Rf_!^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_!^Λ'` for
`Rf_! = Di_! ⋙ Rg_*` attached to the chosen compactification `X ⟶[i] Z ⟶[g] Y` of `f`: the
derived (Push) comparison for the proper `g` followed by the derived (Shriek) isomorphism for
the open immersion `i`. -/
noncomputable def derivedLowerShriekHom :
    R(f)_!⟦Λ⟧ ⋙ L(Mod.extendScalars (coefficientMap a Y)) ⟶
      L(Mod.extendScalars (coefficientMap a X)) ⋙ R(f)_!⟦Λ'⟧ :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D(((HasCompactification.compactification f).i)_!open⟦Λ⟧)
      (derivedPushHom a (HasCompactification.compactification f).g) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (derivedOpenImmersionShriekIso a (HasCompactification.compactification f).i).hom
      R(((HasCompactification.compactification f).g)_*⟦Λ'⟧) ≫
    (Functor.associator _ _ _).hom

/-- **(Shriek)** is an isomorphism whenever (Push) is one for the proper part `g` of the chosen
compactification: its open immersion contributes a formal isomorphism. -/
instance isIso_derivedLowerShriekHom
    [IsIso (derivedPushHom a (HasCompactification.compactification f).g)] :
    IsIso (derivedLowerShriekHom a f) := by
  unfold derivedLowerShriekHom
  infer_instance

end LowerShriek

end CondensedRing

end AlgebraicGeometry.ProEtale
````

Source `WeilConjectures/ConstructibleSheaf/ProEtaleModule/DerivedCategory.lean`

Git blob: `4e2c26fd4485057184d30f9e329ebffb2395e1f4`; SHA-256: `167bc109ae722728ba5032d6131529559b1bb1d913655b6a25b91c8231861eb6`.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def

/-!

# Bounded constructible derived categories of sheaves of modules on the pro-étale site

Let `A` be a closed symmetric monoidal Grothendieck abelian category, `X` a scheme, `R` a
commutative ring object of `Sheaf (Scheme.ProEt.topology X) A`. The derived category of
sheaves of `R`-modules is
```
D(X_proét, R) := DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R).
```
The *bounded constructible* derived category `ProEtale.BoundedConstructible R` is the full
subcategory of `D(X_proét, R)` (`ProEtale.boundedConstructible R`) consisting of the complexes
`K` such that

1. `K` is bounded, i.e. `Hⁱ(K) = 0` for `i` outside a finite interval (for the canonical
   t-structure, see `ProEtale.mem_boundedConstructible_iff`);
2. every cohomology sheaf `Hⁱ(K)` is constructible (`ProEtale.IsConstructible R`).

Morphisms are computed in `D(X_proét, R)`. For `R = 𝒪_{E,X}` this is `D_cons(X_proét, 𝒪_E)`;
for `R = E_X` it is `D_cons(X_proét, E)`.
No derived completeness condition is imposed.

## Sorried input

The bounded constructible complexes on a topologically noetherian scheme form a triangulated
subcategory (`ProEtale.isTriangulated_boundedConstructible`). This rests on the fact that
constructible sheaves on such a scheme are closed under kernels, cokernels and extensions,
which is not formalized; the instance is `sorry`ed. Noetherianity is assumed only there: the
definition `ProEtale.boundedConstructible` makes sense on any scheme. The derived category
itself uses the `sorry`ed instances of
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory`.

-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}}
  (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R] [IsCommMonObj R]

/-- The bounded constructible complexes of sheaves of `R`-modules on `X`: the complexes `K`
which are bounded for the canonical t-structure and all of whose cohomology sheaves `Hⁿ(K)`
are constructible. -/
noncomputable def boundedConstructible :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)) :=
  DerivedCategory.TStructure.t.bounded ⊓ fun K ↦ ∀ n : ℤ,
    IsConstructible R ((DerivedCategory.homologyFunctor _ n).obj K)

omit [IsCommMonObj R] in
/-- A complex is bounded constructible iff its cohomology sheaves vanish outside a finite
interval `[a, b]` and are all constructible. -/
lemma mem_boundedConstructible_iff
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)) :
    boundedConstructible R K ↔
      (∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
      ∀ n : ℤ, IsConstructible R ((DerivedCategory.homologyFunctor _ n).obj K) := by
  refine and_congr_left' ⟨?_, ?_⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨a, b, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff K a).1 ha i hi
    · exact (DerivedCategory.isLE_iff K b).1 hb i hi
  · rintro ⟨a, b, h⟩
    exact ⟨⟨a, (DerivedCategory.isGE_iff K a).2 fun i hi ↦ h i (Or.inl hi)⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).2 fun i hi ↦ h i (Or.inr hi)⟩⟩

/-- The bounded constructible derived category `D_cons(X_proét, R)`. -/
abbrev BoundedConstructible : Type _ :=
  (boundedConstructible R).FullSubcategory

/-- The bounded constructible complexes on a topologically noetherian scheme form a triangulated
subcategory. -/
instance isTriangulated_boundedConstructible [TopologicalSpace.NoetherianSpace X] :
    (boundedConstructible R).IsTriangulated :=
  sorry

end AlgebraicGeometry.ProEtale
````

Source `WeilConjectures/CategoryTheory/RingObjects/Condensed/FiniteSubextension.lean`

Git blob: `42d1ddf5500ccbd3f99ed00cec2139bdfd21655a`; SHA-256: `b1c188d5438cbfb2bded50cddbeb6481dc9e52cfa51422941dfcbbc651848c6a`.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

/-!

# The inclusions `E̲ ⟶ F̲ ⟶ ℚ̲̄_ℓ` of condensed coefficient rings

Let `ℓ` be a prime. The finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` form the directed poset
`PadicAlgCl.FiniteIntermediateField ℓ`. Each of them is a normed field, with the norm restricted
from `ℚ̄_ℓ`, so its condensed ring `E̲ = C(-, E)` is the commutative ring object
`Profinite.continuousMapRingObj E` of condensed abelian groups of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`. This file records the
inclusions between them:

* for `E ≤ F`, the inclusion `E̲ ⟶ F̲` (`Profinite.padicSubfieldRingObjMap`), postcomposition
  with the inclusion `E ⊆ F`, strictly functorial in `E ≤ F`;
* the inclusion `E̲ ⟶ ℚ̲̄_ℓ` (`Profinite.padicSubfieldRingObjToPadicAlgCl`): a continuous map
  `S → E` is a section of `ℚ̲̄_ℓ` over `S`, taking values in the finite subextension `E`;

compatibly with each other (`Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl`). All of them
are morphisms of ring objects. Their pullbacks along `p_X` are the coefficient changes
`E_X ⟶ F_X ⟶ ℚ̄_ℓ,X` on a scheme `X`.

## `ℚ̲̄_ℓ` as the colimit of the `E̲`

The inclusions `E̲ ⟶ ℚ̲̄_ℓ` form a cocone `Profinite.padicAlgClRingObjCocone` over the diagram
`E ↦ E̲` (`Profinite.padicSubfieldRingObjFunctor`) of condensed abelian groups, indexed by the
filtered poset of finite subextensions, and this cocone is a colimit
(`Profinite.isColimitPadicAlgClRingObjCocone`): `ℚ̲̄_ℓ = colim_E E̲`. This is the comparison
identity `eq:Qbar-comparison` of `WeilConjectures/RefactorInstruction.tex` (Proposition
`prop:comparison-only`); it is a theorem, not the definition of `ℚ̲̄_ℓ`, which is defined by its
sections. It holds because filtered colimits of condensed abelian groups are computed
sectionwise on profinite sets (the coverings of `*_proét` being refined by finite ones), and
sectionwise `ℚ̲̄_ℓ(S)` is the union of the subgroups `C(S, E)` of `C(S, ℚ̄_ℓ)` by definition.

## Sorried input

* `Profinite.isColimitPadicAlgClRingObjCocone`: `ℚ̲̄_ℓ = colim_E E̲`, see above.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

instance : CoeSort (FiniteIntermediateField ℓ) Type := ⟨fun E ↦ E.1⟩

/-- The poset of finite subextensions, as a category, is filtered: it is directed and
nonempty. -/
instance : IsFiltered (FiniteIntermediateField ℓ) := isFiltered_of_directed_le_nonempty _

end PadicAlgCl

namespace Profinite

open AlgebraicGeometry.ProEtale PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The inclusions `E̲ ⟶ F̲` -/

/-- The inclusion `E̲ ⟶ F̲` of condensed rings, for finite subextensions `E ≤ F`: postcomposition
with the inclusion `E ⊆ F`, which is continuous for the topologies restricted from `ℚ̄_ℓ`. -/
noncomputable def padicSubfieldCondensedRingMap {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    continuousMapRingSheaf.{u} E ⟶ continuousMapRingSheaf F :=
  continuousMapRingSheafMap (IntermediateField.inclusion h).toRingHom
    (continuous_subtype_val.subtype_mk _)

/-- The inclusion `E̲ ⟶ F̲` of ring objects of condensed abelian groups, for finite subextensions
`E ≤ F`: the abelian sheaf morphism underlying `Profinite.padicSubfieldCondensedRingMap`. -/
noncomputable def padicSubfieldRingObjMap {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    continuousMapRingObj.{u} E ⟶ continuousMapRingObj F :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicSubfieldCondensedRingMap ℓ h)

instance {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    IsMonHom (padicSubfieldRingObjMap.{u} ℓ h) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (padicSubfieldCondensedRingMap ℓ h)))

lemma padicSubfieldRingObjMap_id (E : FiniteIntermediateField ℓ) :
    padicSubfieldRingObjMap.{u} ℓ (le_refl E) = 𝟙 _ := rfl

lemma padicSubfieldRingObjMap_comp {E F H : FiniteIntermediateField ℓ} (h₁ : E ≤ F)
    (h₂ : F ≤ H) :
    padicSubfieldRingObjMap.{u} ℓ (h₁.trans h₂) =
      padicSubfieldRingObjMap ℓ h₁ ≫ padicSubfieldRingObjMap ℓ h₂ := rfl

/-! ### The inclusions `E̲ ⟶ ℚ̲̄_ℓ` -/

/-- The inclusion `C(-, E) ⟶ ℚ̲̄_ℓ` of presheaves of rings on profinite sets, for a finite
subextension `E`: a continuous map `S → E`, composed with the inclusion `E ⊆ ℚ̄_ℓ`, takes values
in the finite subextension `E`. -/
noncomputable def padicSubfieldToPadicAlgClRingPresheaf (E : FiniteIntermediateField ℓ) :
    continuousMapRingPresheaf.{u} E ⟶ padicAlgClRingPresheaf ℓ where
  app S := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((((algebraMap E (PadicAlgCl ℓ)).compLeftContinuous S.unop continuous_subtype_val).codRestrict
      (PadicAlgCl.finiteIntermediateFieldValued ℓ S.unop)
      (fun a ↦ (PadicAlgCl.mem_finiteIntermediateFieldValued_iff ℓ _ _).mpr
        ⟨E.1, E.2, fun x ↦ (a x).2⟩)).comp ULift.ringEquiv.toRingHom))
  naturality _ _ _ := rfl

/-- The inclusion `E̲ ⟶ ℚ̲̄_ℓ` of condensed rings, for a finite subextension `E`. -/
noncomputable def padicSubfieldCondensedRingToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    continuousMapRingSheaf.{u} E ⟶ padicAlgClCondensedRing ℓ :=
  ⟨padicSubfieldToPadicAlgClRingPresheaf ℓ E⟩

/-- The inclusion `E̲ ⟶ ℚ̲̄_ℓ` of ring objects of condensed abelian groups, for a finite
subextension `E`: the abelian sheaf morphism underlying
`Profinite.padicSubfieldCondensedRingToPadicAlgCl`. -/
noncomputable def padicSubfieldRingObjToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    continuousMapRingObj.{u} E ⟶ padicAlgClRingObj ℓ :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (padicSubfieldCondensedRingToPadicAlgCl ℓ E)

instance (E : FiniteIntermediateField ℓ) :
    IsMonHom (padicSubfieldRingObjToPadicAlgCl.{u} ℓ E) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (padicSubfieldCondensedRingToPadicAlgCl ℓ E)))

/-- The inclusion `E̲ ⟶ F̲` followed by the inclusion `F̲ ⟶ ℚ̲̄_ℓ` is the inclusion
`E̲ ⟶ ℚ̲̄_ℓ`: both send a continuous map `S → E` to the same map into `ℚ̄_ℓ`. -/
@[reassoc]
lemma padicSubfieldRingObjMap_comp_toPadicAlgCl {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    padicSubfieldRingObjMap.{u} ℓ h ≫ padicSubfieldRingObjToPadicAlgCl ℓ F =
      padicSubfieldRingObjToPadicAlgCl ℓ E := by
  rw [padicSubfieldRingObjMap, padicSubfieldRingObjToPadicAlgCl,
    padicSubfieldRingObjToPadicAlgCl, ← Functor.map_comp]
  rfl


/-! ### `ℚ̲̄_ℓ` as the colimit of the `E̲` -/

/-- The diagram `E ↦ E̲` of ring objects of condensed abelian groups, indexed by the finite
subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` ordered by inclusion. -/
noncomputable def padicSubfieldRingObjFunctor :
    FiniteIntermediateField ℓ ⥤ Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} where
  obj E := continuousMapRingObj E
  map f := padicSubfieldRingObjMap ℓ (leOfHom f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The cocone over the diagram `E ↦ E̲` with vertex `ℚ̲̄_ℓ`, given by the inclusions
`E̲ ⟶ ℚ̲̄_ℓ`. -/
noncomputable def padicAlgClRingObjCocone : Cocone (padicSubfieldRingObjFunctor.{u} ℓ) where
  pt := padicAlgClRingObj ℓ
  ι :=
    { app E := padicSubfieldRingObjToPadicAlgCl ℓ E
      naturality _ _ f :=
        (padicSubfieldRingObjMap_comp_toPadicAlgCl ℓ (leOfHom f)).trans
          (Category.comp_id _).symm }

/-- **`ℚ̲̄_ℓ = colim_E E̲`**: the inclusions `E̲ ⟶ ℚ̲̄_ℓ` exhibit the condensed ring `ℚ̲̄_ℓ` as the
filtered colimit of the condensed rings `E̲` of the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, in
condensed abelian groups. See the module docstring. -/
noncomputable def isColimitPadicAlgClRingObjCocone :
    IsColimit (padicAlgClRingObjCocone.{u} ℓ) :=
  sorry

end Profinite
````

Source `WeilConjectures/ConstructibleSheaf/ProEtaleModule/Def.lean`

Git blob: `bb220bbc210709d58f2b1bbe65c0af0188458a6c`; SHA-256: `bebcdb7cadad83ef156e89d88db63fbc0f953243ce8f51139a33a590231af528`.

````lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal

/-!

# Constructible sheaves of modules on the pro-étale site

Let `A` be a closed symmetric monoidal Grothendieck abelian category, `X` a scheme and `R` a
ring object of `Sheaf (Scheme.ProEt.topology X) A`, so that `R`-module objects are the sheaves of
`R`-modules on `X_proét`.

## Local finite presentation

`ProEtale.IsLocallyFinitelyPresented R M`: there is a pro-étale cover `{Uᵢ ⟶ X}` with
`M|_{Uᵢ}` finitely presented, i.e. the cokernel of a morphism
`(R|_{Uᵢ})^{mᵢ} ⟶ (R|_{Uᵢ})^{nᵢ}` of free modules of finite rank. Torsion is allowed.

## Constructibility

This part follows the definitions in **Section 6.8** of
*Bhargav Bhatt and Peter Scholze, The pro-étale topology for schemes*

Constructibility is defined with respect to a finite stratification `X = ∐ₐ Xₐ` by locally
closed subschemes, using the existing notion `Scheme.Stratification` (`ConstructibleSheaf.Defs`);
restriction to a stratum is the pullback along its immersion `Xₐ ⟶ X`. Restriction along a
morphism `g` of schemes (to a stratum, or to a member of a pro-étale cover) uses only that the
pullback `g^*` of pro-étale sheaves is lax monoidal (`ProEtale.monoidal_upperStar`): it
sends `R` to a ring object `g^* R` and `R`-modules to `g^* R`-modules (`Functor.mapMod`).

`ProEtale.IsConstructible R M`: there is a stratification such that for each stratum `Xₐ`,
`M|_{Xₐ}` is pro-étale locally finitely presented over `R|_{Xₐ}`. For `R = 𝒪_{E,X}` these are
the constructible `𝒪_E`-sheaves; for `R = E_X` (with `E` a field) they are the constructible
`E`-sheaves, lisse on the strata.

-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

section Local

variable {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

/-- A sheaf of `R`-modules on `X_proét` is *locally finitely presented* if there is a pro-étale
cover `{Uᵢ ⟶ X}` such that each `M|_{Uᵢ}` is the cokernel of a morphism
`(R|_{Uᵢ})^m ⟶ (R|_{Uᵢ})^n` of free modules of finite rank. -/
def IsLocallyFinitelyPresented (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
    Mod.IsFinitelyPresented ((ProEtale.upperStar A (𝒰.f i)).obj R)
      (((ProEtale.upperStar A (𝒰.f i)).mapMod (R := R)).obj M)

end Local

section Constructible

variable {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

/-- A sheaf of `R`-modules `C` on `X_proét` is *constructible* if there is a finite
stratification `X = ∐ₐ Xₐ` such that for every stratum `Xₐ`, `C|_{Xₐ}` is pro-étale locally
finitely presented over `R|_{Xₐ}`.

For `R = 𝒪_{E,X}` these are the constructible `𝒪_E`-sheaves. For `R = E_X` these are the
constructible `E`-sheaves, i.e. the sheaves whose restrictions to the strata of a
stratification are lisse. -/
def IsConstructible (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R) : Prop :=
  ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
    IsLocallyFinitelyPresented ((ProEtale.upperStar A (S.immersion a)).obj R)
      (((ProEtale.upperStar A (S.immersion a)).mapMod (R := R)).obj M)

end Constructible

end AlgebraicGeometry.ProEtale
````

## Second reading by NC

Independent second reader, 2026-10-16. Read delivery-errors B–E, GOAL.md, dag-sync.md, the worker report, the unit and chapter, all three delivered nodes, every statement cited by the six proof steps, and the definition statements used by the new nodes. The two new statements remain unsplit obligations, not finished proofs. The following checks concern the repaired version, with 18 citation occurrences in citations.json; the first worker's review above is retained as history.

- Item statement: checked each hypothesis and both endpoints against the exact-source SmoothPurity/Defs.lean exhibit at commit 7347520d9b0d17cc31d0fc34ea20f1381a83fe13, lines 76–92; PASS. Prime ell, positive prime characteristic unequal to ell, both separated finite-type structure morphisms, the morphism over k, natural d, and SmoothOfRelativeDimension are all retained. The ambient left endpoint is the underlying constructible exceptional image of the tensor unit, and the right endpoint is the positive d twist with shift +2d. The prior STATEMENT-DISPUTED correction concerns the invalid direct specialization over k = F_p(t), not a weakened isomorphism statement.
- Step 1: checked the full finite-smooth node against SGA XVIII 3.2.5, printed pp. 585–586, and 2.13.2, and the added twist citation against clauses 1–2 of lem-pur-twist-sheaf-locally-free; PASS after repair. Wrote the unit's constructibility and Tor amplitude [0,0], and the local-generator proof of twist reduction, including d=0 and the quotient cocycle. The finite lemma supplies normalized gamma and its coefficient compatibility; the strict morphism is identity between explicit copies, so this step never infers a coherent lift from unrelated derived-category maps.
- Step 2: checked all seven cited statements, including the normalized-tower hypothesis in local-effectivity and the full local-model hypothesis in reconstruction, and the compatible etale-origin witnesses in the integral-category definition; PASS. The schemes are Noetherian by local Noetherianness plus quasi-compactness; the cited dimension theorem supplies finite dimension. Their fields need not be algebraic over a finite field. Root sheaves and their tensor powers give the compatible etale witnesses, with intervals [-2d,-2d] and [0,0]. The completed coefficient object is the rank-one identity-cover local model.
- Step 3: checked the exact evaluation and total derived-limit statements, and Stacks homology.tex, label lemma-inverse-systems-abelian (02MZ); PASS. Cone cohomology is computed levelwise, and the actual strict map from Step 1 is an isomorphism. Applying Rlim preserves its inverse. This elementary step uses neither exactness of ordinary infinite products nor uniqueness of a lift.
- Step 4: checked the entire conditional reconstruction node against the hypotheses established in Steps 1–2 and the exact UpperShriek.lean lines 100–146 and BoundedConstructible.lean lines 254–315; PASS. The order is proper chosen right adjoint followed by open pullback, with the specified composite adjunction. The new node explicitly supplies the missing exceptional-counit comparison. Bhatt–Scholze 6.8.14–15 was read and does not prove that comparison. No ambient unbounded pro-etale adjoint is invoked.
- Step 5: checked all six cited statements and the exact TateTwist/RootsOfUnity.lean, TateTwist/ProEtale.lean, ModuleObjects/Free.lean, and finite-subextension coefficient exhibits; PASS after writing the inverse tensor map. Basis evaluation gives the completed coefficient ring and its quotients; Stacks proetale.tex labels lemma-proetale-enough-w-contractible (0990) and lemma-get-many-weakly-contractible (098I) were opened to check the covering used. Local freeness gives ordinary tensors equal to derived tensors. The finite free-module functor is tensor on abelian sheaves, the transitions are power maps, n=0 contributes the zero sheaf, scalar extension is through the bottom finite field, and the nonnegative tensor power is included in degree zero. Both balanced inverse equations are now explicit.
- Step 6: checked types against the exact target and the two previous isomorphisms; PASS after repair. First invert the constructible isomorphism and apply its inclusion into the ambient derived category; only then compose with the ambient Tate identification. The inverse is written as the reversed composite. This order avoids applying a constructible-category inclusion to an already ambient-only endpoint. All operations in this step are elementary.
- New node lem-pur-finite-smooth-adjunction-general-base: checked B1–B7 against its actual SGA sources and the definitions named in stmt_deps; PASS, retain. SGA gives smooth compactifiable purity for an invertible annihilator over a general base; the derived quotient square and cocycle are explicitly additional obligations, not falsely attributed to restriction-of-scalars Corollary 3.1.12.1. The node is statement-only and strictly below condensed rational purity. Existing thm-pur-finite-coefficient-smooth-purity, thm-pur-finite-reduction-of-purity, lem-pur-finite-universal-smooth-trace, lem-coef-finite-exceptional and lem-pur-adic-purity-scalar-naturality fix the finite-field datum. thm-asd-smooth-tensor leaves its orientation unidentified. None replaces the stated normalized general-field input.
- New node lem-pur-condensed-exceptional-reconstruction: checked B1–B7 against its definition dependencies and exact master adjoint and coefficient constructors; PASS, retain. It states a generic conditional coefficient/adjunction comparison, with no smoothness, d or Tate-purity conclusion. Its effectivity, uniform bounds, strict coherent system and canonical reduction hypotheses are all explicit. The source honestly identifies an agent-formulated obligation. Existing prop-coef-integral-exceptional-adjoint fixes k = Fbar_q and has integral coefficients; lem-weil-pbc-condensed-e-realization compares pullback/direct image, while prop-weil-pbc-qbar-condensed-two-colimit compares coefficient categories. Neither supplies this exceptional comparison. It is not an elementary uniqueness-of-adjoints lemma: the geometric counit comparison is substantive.

Independent searches: ran whole-DAG searches for source numbers and smooth trace/exceptional reconstruction, and whole-blueprint searches for smooth purity, exceptional reconstruction, coefficient reduction and condensed coefficients. Reopened the near matches above; found no duplicate or one-line specialization. blueprint_refs ancestor again returns null for this maintainer-seeded batch item, so no ancestry or unit metadata was changed. Ran msearch.py with new semantic phrasings for both new nodes, a valid Loogle adjunction query, and a word-bounded Mathlib AlgebraicGeometry grep. Read the returned signatures: ordinary structure-sheaf adjunctions, discrete condensed modules and abstract adjunction machinery do not state either assertion; the targeted grep returned zero hits. These actual records are appended to each node and searches.jsonl. One exploratory Loogle query used an unknown identifier and remains only in the raw log, not as evidence of absence. No Mathlib leaves were found. Read slopmaster2 Smooth/Basic.lean lines 294–344: the ordinary-etale smoothPurityIso takes orientation/tensor isomorphisms, and its existence theorem neither gives the new coefficient cocycle nor the condensed endpoint. No attachment is justified.

Small cases: checked K=0 and L=0; f the identity with d=0; n=1; d=1 for the nonproper affine-line projection over F_p(t); and empty source or target. The conclusions allow zero cohomology in the stated interval and do not assert a nonzero group on the empty scheme. At n=0 only the upstream limit system has a term, and that term is zero; the finite theorem starts at n=1. Characteristic zero is permitted by the finite input alone and is not substituted into the positive-characteristic condensed comparison. No additional statement dispute was found.

Changes made and why:

1. Step 1 now verifies membership of the unit in the finite-Tor constructible domain and cites the existing twisting-sheaf result for explicit normalized reductions. This closes a C1/C4 hypothesis-and-normalization omission without adding a node.
2. Step 5 now writes the inverse of the d-fold scalar-extension tensor map, including d=0, so the claim of an inverse is checkable from balanced tensors (E5).
3. Step 6 now includes the constructible isomorphism before composing with the ambient Tate endpoint, and states the inverse composite, fixing the categorical typing/order.
4. Retained both new node statements, appended independent actual search records, updated proof_deps and all 18 verbatim citation records, and regenerated the report's citation evidence to match.
5. Re-fenced the complete exact-source exhibits with outer fences longer than their embedded docstring fences. This preserves every source byte and hash while making the source exhibits render as code rather than accidentally terminate at an internal triple-backtick example. Recomputed all twelve Git-blob and SHA-256 hashes from the sandbox copies and compared those copies with the manifest texts; all agree. The local read-only master checkout lacks SmoothPurity/Defs.lean, so this reading used the exact-commit source exhibits, not a different revision or any sorry as proof.

Only the authorized sandbox was edited. No agents, Lean edits, compiler, Lake, global build, or direct git command in the shared repository were used. Final validation and delivery results are recorded below.

Independent exact-commit binding check: the second reader additionally read all twelve blobs with read-only git show from the existing server source object store /home/ubuntu/sidebuild-base/repo.git at commit 7347520d9b0d17cc31d0fc34ea20f1381a83fe13, and independently computed both hashes. Every hash matches the source exhibits above. Results are in sandbox source-evidence/second-reader-source-hashes.json. This made no change to any repository or source checkout.

Validation: the repaired split passed the mandated DAG-only dry run: OK (not pushed) deliver/NC/nt-target-smooth-purity-qbar at b6cc624ab6: preflight passed. The source and citation integrity checks also passed (12 exact-commit source exhibits, 18 verbatim citations, statement-only frontier nodes). A final dry run follows this completed report before delivery.
