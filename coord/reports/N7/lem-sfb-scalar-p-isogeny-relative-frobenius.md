## Worker report

The module `Sheaf.AlgebraicGeometry.ScalarPIsogenyRelativeFrobenius` states
`AlgebraicGeometry.scalarPIsogeny_relativeFrobenius`, with its only proof `sorry`.
No definitions or additional theorem nodes are needed. The item's mathematical
statement, source, proof and proof dependencies are unchanged. Its stmt_deps gain
three already-landed definition nodes for the exact terminology used.

Clause-by-clause rendering:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
  Positive characteristic is `(p : ℕ) [Fact p.Prime] [CharP F p]`; a positive
  characteristic of a field is prime, so this excludes no case of the node.
- The group scheme is `G : Grp (Over (Spec (.of F)))`. Its full reductivity
  hypothesis is `ReductiveTorusCentralizer.IsReductive G`: affine finite type,
  smooth, geometrically connected, and no nontrivial smooth connected normal
  closed unipotent subgroup after algebraic closure. `IsUnipotent` uses a
  faithful matrix representation and all algebraically closed extension fields.
  Over the algebraically closed F these are exactly the node's hypotheses.
- The torus subgroup is the group-scheme map `i : T ⟶ G`, with
  `ReductiveTorusCentralizer.IsMaximalTorus i`, including closed inclusion and
  maximality among all tori. `hsplit` says `∃ r, Nonempty (T ≅ splitTorus F r)`.
  The split torus is the existing iterated G_m product, with rank zero allowed.
- The endomorphism is `f : G ⟶ G`, already a group homomorphism by bundling;
  `[Surjective f.hom.hom.left]` is scheme-surjectivity, and
  `[IsFinite (GrpObj.ker f.hom.hom).hom]` is finiteness of the actual
  scheme-theoretic kernel. For a scheme over a field this means affine with
  finite-dimensional coordinate algebra, not just a finite set of F-points.
- Preservation of T is the explicit factorization `fT : T ⟶ T` and
  `hfT : fT ≫ i = i ≫ f`. Since i is a closed subgroup inclusion the restriction
  is unique; supplying it is exactly the asserted factorization.
- A character is a scheme-over-F map `χ : T.X ⟶ multiplicative F` satisfying
  `IsMonHom χ`. `hscalar` says `fT.hom.hom ≫ χ = χ ^ p` for every such
  character. The power is pointwise multiplication of morphisms into G_m:
  in the additive notation of the character lattice it is pχ.
- The twist is the literal object
  `((Over.pullback (Spec.map (CommRingCat.ofHom (frobenius F p)))).mapGrp.obj G)`.
  It has the pulled-back group law, not an arbitrarily chosen model or law.
  For affine G this fibre product is canonically Spec of C tensor_(F,Frob) F.
- The conclusion supplies an actual group-scheme isomorphism `h` from this
  twist to G. Writing r = f followed by h inverse, it states that r followed
  by the projection from the twist back to G satisfies `IsFrobenius p`.
  Both f and h are morphisms over F, so r's other projection is G's structure
  map. Hence r is exactly the unique relative Frobenius lift. In particular,
  the formula on coordinates is b tensor c ↦ c b^p, and f = h after r.
  Conversely the node's factorization implies precisely this conclusion.
  This is an equivalent universal-property rendering, not a statement correction.
  The Frobenius predicate is nonvacuous here: G is affine over the field of
  characteristic p; every affine chart has its actual p-power ring map.
- There is no finite-field model, Borel compatibility, kernel separability,
  reducedness, or condition prime to p anywhere in the binders or conclusion.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-weil-algebraic-closure`: `IsAlgClosed`, explicitly included in the
  mathlib_match's explanation, Mathlib.FieldTheory.IsAlgClosed.Basic.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, `Grp`, `IsMonHom`, and
  `GrpObj.ker`; Mathlib.CategoryTheory.Monoidal.Grp and
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. The latter's full
  group-scheme docstring and kernel definition were read.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme.
- Added landed node `def-sfb-reductive-torus-centralizer-terminology`:
  `ReductiveTorusCentralizer.IsReductive` and `IsMaximalTorus`, in
  Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology.
- Added landed node `def-sfb-tori-multiplicative-type`:
  `MultiplicativeType.splitTorus`, in Sheaf.AlgebraicGeometry.ToriMultiplicativeType.
- Added landed node `def-sc-gm-ga`: `StandardGroupSchemes.multiplicative`, in
  Sheaf.AlgebraicGeometry.StandardGroupSchemes, with its actual Laurent Hopf law.
- Canonical base change is Mathlib's `Over.pullback` and `Functor.mapGrp`.
  The existing `Scheme.Hom.IsFrobenius`, in
  WeilConjectures.AlgebraicGeometry.Frobenius, characterizes absolute Frobenius.
  Its warning about vacuity outside characteristic p was explicitly checked.
  The existing general `relativeFrobenius` and its full source docstring in
  WeilConjectures.AlgebraicGeometry.RelativeFrobenius were also read: its
  pullback projections give the equivalent characterization used here.

All three proof-dependency node statements were read. They have neither a Lean
record nor a Mathlib match in the read repository, so no unavailable proof-only
modules are imported. The four-step docstring preserves their proof plan.
They are not statement prerequisites: the present statement uses existing
notions and needs none of those results as data.

Edge cases checked before writing: p=2 and arbitrary positive characteristic;
nonreduced finite kernels (including μ_p); G a torus; rank zero and the trivial
group, where the character condition is automatic and Frobenius is the
isomorphism of the terminal F-group; no roots and no Borel chosen. An empty
underlying scheme cannot be a group scheme over a nonzero field because of
its unit section. All schemes and test rings use the shared universe u;
there is no independently too-small test universe or extra universe equality.

Searches (2026-10-24):

- msearch.py leanfinder: "An isogeny of a reductive algebraic group acting by p
  on its torus characters factors through relative Frobenius by an isomorphism".
  Eight hits, chiefly `coe_frobenius_comp_coe_frobeniusEquiv_symm`,
  `frobeniusEquiv_apply` and Witt-vector/finite-field formulas; no group-scheme
  isogeny theorem.
- msearch.py leansearch: "An isogeny inducing p on maximal torus characters is
  relative Frobenius followed by an isomorphism". Eight hits including
  `FiniteField.Extension.frob`, `LinearMap.frobenius`, and `bijective_frobenius`;
  none states the result.
- msearch.py loogle: `"relativeFrobenius"`: zero hits.
- msearch.py grep: `Reductive|relativeFrobenius|Isogeny`, AlgebraicGeometry:
  zero Mathlib hits.
- rg in lean/WeilConjectures and lean/Sheaf for reductivity, maximal tori,
  isogenies and relative Frobenius found the exact existing terminology listed
  above and general relative Frobenius, but no scalar-p isogeny theorem.
  The item-id and proposed theorem-name searches in the upstream sources
  returned no declaration. Full signatures and docstrings were read.
- The source was read directly with pdftotext: Milne printed pp.47--49,
  492--493 (PDF pages 59--61, 504--505). Section 2.26 gives exactly the
  pullback characterization; the affine formula on p.47 is b tensor c ↦ c b^p;
  23.25--23.26 give the comparison and uniqueness used in the proof plan.
  The current blueprint unit sk-thm-sf-ctf-stability/_section.md was read.

No STATEMENT-DISPUTED flag or mathematical node fault remains. The prescribed
server scompile.py compiled both the sandbox and library module cleanly
(1.8 s and 1.9 s); only the expected postponed theorem is present.

## Second reading by N7

The worker reread the node and final file in-thread after compilation. This is
a self-check; the independent review belongs to the maintainer, as specified
by this dispatch, which prohibits starting other agents.

The second pass checked the orientations of `hfT` and the Frobenius pullback
projection: Over.pullback uses `pullback G.X.hom σ`, with `pullback.fst` the
projection to G and `pullback.snd` the structure map. Thus the predicate is
applied to the endomorphism of G, not to a morphism with the wrong base.
The character binder ranges over every homomorphism to G_m, not an assumed
basis or a restricted set of weights. h is an isomorphism in the category of
group schemes, not merely of underlying schemes. The rank-zero torus remains
allowed. No mismatch required a mathematical change; compilation required
opening Mathlib's exported `MonObj` scope for the pointwise Hom power.
