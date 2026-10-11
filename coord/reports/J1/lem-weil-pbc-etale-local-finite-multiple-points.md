## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleLocalFiniteMultiplePoints` states
`AlgebraicGeometry.exists_etale_local_finite_multiple_points`, with its sole proof `sorry`.
No definitions, auxiliary axioms, new nodes, or dependency modules are introduced.

Clause-by-clause reading of the corrected node:

- Schemes and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`; the universe is explicit.
- Locally of finite type: `[LocallyOfFiniteType f]` (not finite type or separated).
- Base point and finite input list: `(s : S) (n : ℕ) (x : Fin n → X)`.
- Every input maps to s: `hx : ∀ i, f (x i) = s`.
- Distinct inputs (the recorded correction): `hdistinct : Function.Injective x`.
- Isolatedness in the scheme-theoretic fiber: `hisolated` asserts that the singleton
  of `(f.fiberHomeo s).symm ⟨x i, hx i⟩` is open in `f.fiber s`. This uses precisely
  the fiber's topology, without demanding an open singleton in X.
- Etale neighborhood: existential `U : Scheme.{u}`, `g : U ⟶ S`, `Etale g`,
  `u : U`, and `g u = s`. No residue-field-isomorphism constraint is imposed.
- Nonnegative integers: `m : Fin n → ℕ`. The indices `Fin (m i)` encode 1 through m_i
  with the standard zero-based relabeling.
- Open subschemes: `V i j : (pullback f g).Opens`, with actual restricted scheme
  `(V i j).toScheme` and canonical open inclusion `(V i j).ι`.
- Finite over U: `IsFinite ((V i j).ι ≫ pullback.snd f g)`.
- Distinguished point: `v i j : (V i j).toScheme`, with proof `hv` that its image is u.
- Unique point of each open over u: every `w` of that restricted scheme with image u
  equals `v i j`. This is uniqueness of all points over u, not just those with a
  specified residue extension.
- Finite purely inseparable residue extension: use the algebra structure induced by
  `((U.residueFieldCongr hv.symm).hom ≫
  ((V i j).ι ≫ pullback.snd f g).residueFieldMap (v i j)).hom.toAlgebra`.
  The equality transport starts at κ(u) and ends at κ(v_i,j). The conjunction
  `Module.Finite ... ∧ IsPurelyInseparable ...` states exactly the requested extension.
- Image in X: `pullback.fst f g ((V i j).ι (v i j)) = x i`.
- Pairwise distinctness: injectivity of the function on dependent pairs
  `(i : Fin n) × Fin (m i)` taking a pair to its point in the common ambient pullback.
  Comparing the ambient points avoids meaningless equalities between different opens.
- No unlisted points over x_i and u: the last universal quantifier says every ambient
  pullback point with those two projection images equals `(V i j).ι (v i j)` for some j.
  By `Scheme.Hom.fiberHomeo`, this is equivalently exhaustion in the scheme fiber over u.

Dependency declarations read and used (the mathlib_match of a Mathlib leaf is its record):

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; open subschemes use `Scheme.Opens.toScheme` and
  `Scheme.Opens.ι`, `Mathlib.AlgebraicGeometry.Restrict`, the restriction of the scheme.
- `def-pc-scheme-fibre`: `Scheme.Hom.fiber`, `Scheme.Hom.fiberHomeo`,
  `Mathlib.AlgebraicGeometry.Fiber`. The former is the pullback along
  `S.fromSpecResidueField s`; the latter is a homeomorphism onto the inverse-image subset.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, the affine-local finite-type class.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, the affine-local etale ring-map class.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; existence for schemes is
  supplied by Mathlib's scheme pullbacks.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, affine morphism with finite maps on affines.
- `def-weil-residue-field`: `Scheme.residueField`, `Scheme.Hom.residueFieldMap`,
  `Scheme.residueFieldCongr`, `Mathlib.AlgebraicGeometry.ResidueField`; these are stalk
  residue fields, their induced maps, and canonical equality transport.
- `def-weil-pbc-finite-purely-inseparable-extension`: `IsPurelyInseparable`,
  `Mathlib.FieldTheory.PurelyInseparable.Basic`, and `Module.Finite`. The class agrees with
  the power-in-the-base characterization in positive characteristic and triviality in
  characteristic zero; no characteristic restriction is added.

All three imports are used: Fiber supplies fiber, residue fields, pullbacks and finite
morphisms; Etale supplies the etale class (and local finite type); PurelyInseparable.Basic
supplies the inseparability class. Every variable and universe is bound explicitly.

Edge cases: n=0 permits U=S, g=id and u=s, with empty families. Empty X permits only an
empty input list, and empty S supplies no s, so the statement is vacuous. m_i=0 is allowed,
but exhaustion prevents this when lifts exist. The opens need not be disjoint or cover
all of the pullback. Characteristic zero forces each purely inseparable extension to be
trivial; positive characteristic uses Mathlib's actual inseparability notion. Multiple
separable lifts are allowed. Repeated inputs revealed the fault recorded below.

Searches made on 2026-10-11:

- msearch.py leanfinder: `etale neighbourhood finitely many isolated fibre points finite
  open subschemes purely inseparable residue fields`: 8 hits, etale-locus and ring-level
  existence theorems, no simultaneous scheme-point theorem.
- msearch.py loogle: `AlgebraicGeometry.Etale, AlgebraicGeometry.IsFinite`: one candidate
  `AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt`. Its signature additionally
  requires separatedness and concerns a single point, so it is not this node's statement.
- msearch.py grep: `multiple.points|02LM|exists_etale_isCompl`, AlgebraicGeometry:
  only that single-point theorem and its later use in ZariskisMainTheorem.lean.
- rg of Mathlib AlgebraicGeometry/Fiber, ResidueField, and morphism files for
  `quasiFiniteAt_iff_isOpen|asFiber|residueFieldMap|class Etale|class IsFinite|
  class LocallyOfFiniteType|def fiber|def fiberHomeo`: supplied the exact standard notions.
- rg of WeilConjectures and lean/Sheaf for
  `etale.*finite|isolated.*[Ff]ib|multiple.points|02LM`: general etale/finite modules,
  no exact theorem. grep -rn for the item id in WeilConjectures returned no match.
- rg for `exists_etale_local_finite_multiple_points` in dag/lean_names_upstream.json,
  WeilConjectures, Mathlib, and lean/Sheaf returned no match.

The local literature checkout has no stacks-project/more-morphisms.tex. Read the source
at https://stacks.math.columbia.edu/tag/02LM, including its statement and complete proof.
The module docstring carries all six proof steps from the supplied DAG node, including
its final verification of exhaustion, residue fields, and distinctness.

## Statement corrected

Old statement, verbatim:

Let $f:X\to S$ be a morphism of schemes [def-pc-scheme]. Let $s\in S$ and let $x_1,\ldots,x_n\in X$ satisfy $f(x_i)=s$. Let $X_s=X\times_S\operatorname{Spec}\kappa(s)$ be the scheme-theoretic fibre [def-pc-scheme-fibre], and assume that $f$ is locally of finite type [def-weil-finite-type-morphism] and that each $x_i$ is an isolated point of $X_s$. Then there are an etale neighbourhood $(U,u)\to(S,s)$ (so $U$ is a scheme, $U\to S$ is etale [def-weil-etale-morphism], and $u\in U$ maps to $s$), integers $m_i\geq0$, and open subschemes $V_{i,j}\subseteq X\times_SU$ [def-pc-fibre-product] such that: each $V_{i,j}\to U$ is finite [def-weil-finite-integral-morphism]; it has a unique point $v_{i,j}$ over $u$ with $\kappa(u)\subseteq\kappa(v_{i,j})$ a finite purely inseparable extension [def-weil-residue-field] [def-weil-pbc-finite-purely-inseparable-extension]; $v_{i,j}$ maps to $x_i$; no other point of $(X\times_SU)_u$ maps to $x_i$; and $v_{i,j}=v_{i',j'}$ implies $(i,j)=(i',j')$.

Repeated inputs are incompatible with simultaneous exhaustion and globally distinct output points: for f=id of Spec k, n=2 and x_1=x_2 the same sole lift must occur in both lists, contradicting (iv). Stacks 02LM implicitly treats the listed points as distinct: its global distinctness clause (iv), together with exhaustion (iii), requires this. The elementary lemma 02LL itself permits repetitions. Also the phrase no other point must mean no point outside the entire list for i, not outside an individual singleton; separable residue extensions may give m_i>1. Make both conventions explicit.

The corrected statement makes explicit the distinct-point convention required by the source enumeration, and renders the exclusion as exhaustion by the entire list for each i. This is a tool node, not the blueprint unit statement. No dependency or proof field changes were necessary. The proof already says that the images for different i are different. Source: Stacks Tag 02LM, enumeration of y_i,j and application of 02LL.

- `lem-weil-pbc-unramified-etale-local-decomposition`: holds: true. Apply to the finite set of distinct input points (deduplicate the list); assign m_i=0 to redundant indices in the decomposition. The exclusion and disjointness uses remain valid.

This is the only direct statement/proof citer found by scanning every node after the required textual grep. The other textual hits refer to the item in provenance, not dependencies. Its hypotheses do not require distinct inputs, but its intended decomposition still follows by deduplicating before applying this tool and putting zero pieces at repeated indices. The literal application in its proof should be understood with this deduplication. No citer was edited.


## Second reading by J1

Read the corrected node FIRST against the full Stacks TeX statement and proof at
`lemma-etale-makes-quasi-finite-finite-multiple-points-var` (02LM), fetched from
https://raw.githubusercontent.com/stacks/stacks-project/master/more-morphisms.tex
into the sandbox scratchpad because this machine has no literature/stacks-project.
Also read 02LL and the introductory context: there is no ambient Noetherian,
separatedness, characteristic, or finite-presentation hypothesis on f.

Independent object/hypothesis/conclusion checklist (all verdicts PASS):

1. Arbitrary schemes X,S and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
   Read def-pc-scheme's Mathlib records; this is the category of schemes itself.
2. Locally finite type only: `[LocallyOfFiniteType f]`. Read the class signature and
   affine-local finite-type field in Mathlib/AlgebraicGeometry/Morphisms/FiniteType.
3. Base point, finite list, common image: `(s : S) (n : ℕ) (x : Fin n → X)` and
   `hx : ∀ i, f (x i) = s`. A finite list needs no separate index universe.
4. Corrected distinct-input convention: `hdistinct : Function.Injective x`.
   With f=id of Spec k and two repeated inputs the sole lift is required by exhaustion
   in both lists, contradicting global distinctness. Thus 02LM's conclusion itself
   forces distinct inputs. This correction makes its intended point-list convention
   explicit rather than choosing an easier geometric case. 02LL does NOT require
   distinct inputs; I repaired the worker's erroneous explanation of that fact.
5. Scheme-theoretic fiber and isolatedness: `f.fiber s` and openness of the singleton
   `(f.fiberHomeo s).symm ⟨x i, hx i⟩`. Opened Mathlib/Fiber: fiber is the pullback
   along `S.fromSpecResidueField s`, and fiberHomeo identifies it with f inverse-image
   of {s}. This is precisely isolatedness in X_s, not isolatedness in X.
6. Etale pointed neighborhood: `∃ U g, Etale g ∧ ∃ u, g u = s ∧ ...`.
   Read def-weil-etale-morphism and Mathlib's Etale signature/affine ring-map field.
   No elementary-neighborhood (residue-field isomorphism) condition is imposed.
7. Counts and open subschemes: `m : Fin n → ℕ`, dependent `V i j` in
   `(pullback f g).Opens`, and `v i j : (V i j).toScheme`.
   Read def-pc-fibre-product, pullback/fst/snd signatures, and Restrict.toScheme/ι:
   these are actual open restrictions and their canonical scheme morphisms.
8. Finite over U: `IsFinite ((V i j).ι ≫ pullback.snd f g)` for each i,j.
   Read def-weil-finite-integral-morphism and IsFinite: affine plus finite affine maps.
9. Exactly one point over u: existential `hv` proves the chosen point maps to u;
   `∀ w, ... w = u → w = v i j` gives uniqueness of every point in that open's fiber.
10. The induced finite purely inseparable residue extension: the algebra is built
    from `U.residueFieldCongr hv.symm` followed by the composite projection's
    `residueFieldMap (v i j)`, then `Module.Finite ∧ IsPurelyInseparable`.
    Read def-weil-residue-field, residueField/Field/residueFieldMap/residueFieldCongr
    signatures, and def-weil-pbc-finite-purely-inseparable-extension and the Mathlib
    class. The first transport runs from κ(u) to κ(projection(v)); the second map
    runs to κ(v). This specifies the geometric extension, not an arbitrary algebra.
11. Image in X: `pullback.fst f g ((V i j).ι (v i j)) = x i`.
12. Global distinctness: `Function.Injective` on the dependent pair type
    `(i : Fin n) × Fin (m i)`, mapping each pair to its ambient pullback point.
    Equality is compared in the common ambient scheme, as the source intends.
13. Exhaustion for each i: every ambient point w with projections u and x i equals
    a listed `(V i j).ι (v i j)`. The fiber homeomorphism makes this equivalent to
    the source's scheme-fiber exclusion. It permits multiple separable lifts.

Quantifiers match the node: f,s,n,x and all hypotheses precede the simultaneous
choice of U,g,u,m,V,v. Uniqueness, residue extension, image, distinctness, and
exhaustion all refer to that same choice. No disjointness of opens or covering of
all X_U is requested. All eight dependency nodes and the actual Mathlib signatures
were read; none needs a replacement module. There are no new definition nodes or
additional dependency modules to audit under H12/H13.

Edge cases: n=0 allows the identity neighborhood with empty families, including
when X is empty. Empty S makes the s binder impossible. Positive n cannot give an
input to empty X. Zero rings/empty affine schemes are therefore not excluded.
The m_i=0 encoding is allowed; for a nonempty input fiber it cannot satisfy the
exhaustion clause, as in the source. Characteristic zero and positive characteristic
are both handled by the standard inseparability class without extra assumptions.
The explicit arbitrary u covers schemes in every universe; the chosen neighborhood,
opens, and pullbacks remain in that same universe. No variables are left unbound.

Independent searches (2026-10-11):

- msearch leanfinder: `simultaneous quasi finite points etale localization finite
  neighborhoods radicial residue extension`. Eight hits, etale ring loci and
  localization lemmas; no simultaneous scheme statement.
- msearch loogle: `"quasiFiniteAt"`. Twelve ring-level quasi-finite-at and base-change
  hits; none has the required simultaneous scheme conclusion.
- rg of Mathlib AlgebraicGeometry, WeilConjectures/AlgebraicGeometry and
  lean/Sheaf/AlgebraicGeometry for `02LM|quasiFiniteAt|purely[Ii]nseparable|
  purely_inseparable`; rg of all WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json for the item id and etale-local finite-neighborhood
  wording. No exact duplicate. Opened the closest Mathlib theorem
  `exists_etale_isCompl_of_quasiFiniteAt` in ZariskisMainTheorem.lean:49: it assumes
  IsSeparated f and treats one point, without our residue-field and exhaustion
  conclusions. It is not a replacement for this node.

Correction/citer check: scanned every repository node's stmt_deps and proof_deps.
There is exactly ONE direct citer, so a second direct citer cannot be opened:
`lem-weil-pbc-unramified-etale-local-decomposition`. Read its full statement and
four proof steps. Its holds:true verdict is correct: deduplicate the input list,
apply this lemma to distinct representatives, and assign zero pieces to redundant
indices. Its conclusion excludes all original points from W but does not require
that pieces assigned to every repeated index exhaust that point. Its intersection
argument uses the globally distinct distinguished points, which the corrected
lemma supplies. No citer was edited.

Mismatches and repairs: no Lean/node mismatch remains. Repaired only the claim
that 02LL needs distinct inputs, in the report and statement_change.what; the
counterexample and the geometric correction remain valid. Kept the Lean signature
and corrected TeX unchanged. The one theorem is unproved with sole proof `sorry`;
there are no definitions, hollow data, private notions, or auxiliary axioms.
The module/declaration docstrings name the source and blueprint id, and the
six-step proof plan includes all node steps. All imports are used and lines fit
100 characters. Checked node lean.statement verbatim against the signature before
`:= by`. scompile.py compiled the single module cleanly in 1.8 seconds, exit 0.
