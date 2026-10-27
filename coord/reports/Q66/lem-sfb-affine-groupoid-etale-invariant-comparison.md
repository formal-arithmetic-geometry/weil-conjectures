## Worker report

The module `Sheaf.AlgebraicGeometry.AffineGroupoidEtaleInvariantComparison` states
`AlgebraicGeometry.affineGroupoid_etale_invariant_comparison`, with one `sorry`
and no definitions or other postponed theorems. Its source is Stacks Project,
`literature/stacks-project/groupoids.tex`, `lemma-etale`, Tag 0DT9, read in full
including the proof. The theorem docstring carries all eight accepted DAG proof
steps, their dependency names, and the finite-data descent and geometric-point
details. The accepted statement, split, and statement dependencies are unchanged.
Only the item's `lean` field is added.

The previous ending concerned stage 1. The current node is `status: split`, has
a passing stage-1 review, has no Lean record, and occurs as stage 2 in
`coord/queue.tsv`. There is no repair note for it. The stage-handoff paragraph of
`coord/brief-stage2.md` explicitly authorizes this stage-2 attachment without
reopening the accepted split.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Scheme S and four schemes U,R,U',R' | `(S U R U' R' : Scheme.{u})`, arbitrary explicit universe `u` |
| Groupoids with source, target, identity, inverse, composition | Maps `s,t,e,i,c` and their primed counterparts, with `_hG : Scheme.IsGroupoid s t e i c` and `_hG'` |
| Groupoids over S | Structure maps `π,π'` and `_hS : s ≫ π = t ≫ π`, `_hS'`; the arrow structure maps are consequently `s ≫ π` and `s' ≫ π'` |
| Morphism F with object map a and arrow map b, over S | Binders `a,b`, `_ha : a ≫ π = π'`; commutation with source and target is included in `_hs.w` and `_ht.w` |
| Preservation of identity | `_he : e' ≫ b = a ≫ e` |
| Preservation of inverse | `_hi : i' ≫ b = b ≫ i` |
| Preservation of composition | `_hc`, universally over every test scheme H and every compatible pair of points `p',p` of the composition pullbacks; its two projection equalities say precisely that p is induced from p' by b, and its conclusion is `p' ≫ c' ≫ b = p ≫ c` |
| Four schemes affine | `[IsAffine U] [IsAffine R] [IsAffine U'] [IsAffine R']` |
| Four source/target maps finite locally free | `[s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree] [s'.IsFiniteLocallyFree] [t'.IsFiniteLocallyFree]` |
| a etale | `[Etale a]`, the current nondeprecated name for the recorded Mathlib notion |
| Source square cartesian | `_hs : IsPullback b s' s a` |
| Target square cartesian | `_ht : IsPullback b t' t a` |
| Scheme-theoretic stabilizers G and G' defined by the displayed pullbacks | On every H, their points are exactly the pairs `(x,r)` with `r ≫ s = x = r ≫ t`; `_hstab` expands this universal property, avoiding a second stabilizer definition |
| Stabilizer square cartesian | `_hstab`: for every H, every `x : H ⟶ U'`, and every loop `r` at `x ≫ a`, there is exactly one `r'` mapping to r and with both endpoints x |
| C and C' are the invariant global sections | `s.appTop.hom.eqLocus t.appTop.hom` and the corresponding primed equalizer, existing Mathlib subrings of `Γ(U,⊤)` and `Γ(U',⊤)` |
| Induced map C → C' | The existential ring homomorphism φ is specified by `(eqLocus ...).subtype.comp φ = a.appTop.hom.comp (eqLocus ...).subtype`, so it sends each invariant function to its pullback by a |
| Spec C' → Spec C etale | `Etale (Spec.map (CommRingCat.ofHom φ))` |
| Natural map U' → U ×_(Spec C) Spec C' is an isomorphism | Final `IsPullback a q' q (Spec.map (CommRingCat.ofHom φ))`, where q and q' are explicitly `toSpecΓ ≫ Spec.map` of the corresponding invariant-subring inclusions |
| Empty schemes and variable ranks allowed | No `Nonempty`, `Nontrivial`, positive/constant rank, connectedness or Noetherian binder |

Encoding checks:

* The groupoid laws make identity, inverse, and composition morphisms over S
  from equality of the two source/target structure maps. For instance,
  `e ≫ s = 𝟙 U` gives that e is over S, and
  `c ≫ s = pullback.snd s t ≫ s` gives the composition compatibility.
  Thus no extra over-S assumption is missing and no unrelated hypothesis is added.
* Source and target commutation, supplied by the two pullback hypotheses, ensure
  that every composable primed pair maps to a composable unprimed pair. The
  universal property supplies p in `_hc`; that hypothesis is not vacuous.
* `_hstab` uses all `Scheme.{u}` tests, including nonreduced tests. The displayed
  pullback definition of G identifies its H-points with loops at an H-point of U.
  For such r and x, the unique lift r' in `_hstab` is precisely the unique
  H-point of G' over their fibre-product point. Conversely the cartesian
  stabilizer square gives exactly this lifting property. Yoneda detects the
  isomorphism using this same scheme category. This is stronger than merely
  checking geometric-point stabilizers, and exactly the stated hypothesis.
* The first conclusion forces φ uniquely: the inclusion of C' in Γ(U',⊤) is
  injective. There is no arbitrary map, arbitrary isomorphism, extra input
  comparison, or `Nonempty` choice. Existence and its specified formula state
  the well-defined canonical restriction of `a.appTop` together with its
  properties. No definition chooses data from an existence theorem.
* Mathlib's `IsPullback` is the universal property for the actual q,q' and a.
  `CategoryTheory.IsPullback.isoPullback` identifies its top-left vertex with
  the chosen `pullback q (Spec.map ...)`, and its projection equations show
  that the isomorphism is exactly the natural comparison in the node. This
  packages the commutativity proof in the conclusion instead of needing an
  extra lemma just to form `pullback.lift`. It is equivalent to the node's
  isomorphism assertion, with both required projection compatibilities.

Dependency declarations used, read with their full signatures and docstrings:

| Node | Module and declaration |
| --- | --- |
| `def-pc-scheme` | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom` |
| `def-a1-scheme-groupoid-laws` | `Sheaf.AlgebraicGeometry.SchemeGroupoidLaws`: `AlgebraicGeometry.Scheme.IsGroupoid` (the recorded interface, not the other absolute groupoid predicate) |
| `def-weil-affine-spectrum` | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`; `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine` for the affine hypotheses |
| `def-pc-finite-locally-free` | `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`: `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`, extending finite, flat and locally finitely presented, without a degree restriction |
| `def-weil-etale-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, affine-locally etale ring maps; its deprecated alias `IsEtale` is not used |
| `def-pc-fibre-product` | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`, `pullback.snd`; `CategoryTheory.IsPullback` states its universal property |

`RingHom.eqLocus` is read from
`Mathlib.Algebra.Ring.Subring.Basic`; its carrier is literally `{f | s♯ f = t♯ f}`.
`Scheme.toSpecΓ` is the canonical unit in
`Mathlib.AlgebraicGeometry.GammaSpecAdjunction`. These existing definitions give
the quotient maps directly, so no new notion or helper node is needed.

All currently stated proof-dependency modules are imported without `public`.
The two proof dependencies `lem-sfb-groupoid-strict-local-reduced-orbit` and
`lem-sfb-henselian-pair-radical-etale-section` have no Lean records or Mathlib
matches in the current DAG, so no imports can yet be attached for them. They
are proof inputs only, and their full uses are retained in the docstring;
neither is needed to type this statement. No statement dependency is missing
or repaired, and no import cycle is introduced by this new module.

Edge cases checked before writing and on the second pass:

* Empty U forces R empty by its source map. A map U' → U forces U' and R'
  empty too; both invariant rings are zero and the claimed square is cartesian.
* Empty U' with arbitrary unprimed groupoid gives C'=0, an empty invariant
  spectrum, an etale empty map and the empty pullback square.
* Identity groupoids have s=t=identity, C=Γ(U,⊤). For an arbitrary etale
  a, all three input squares hold and the output is the evident affine square.
* For an identity morphism of any such groupoid, φ is identity and all squares
  are cartesian. No surjectivity of a is assumed.
* Disjoint copies give product invariant rings and the expected disjoint-union
  comparison; finite locally free ranks may vary over clopen pieces.
* Nonreduced tests remain in `_hstab`, retaining scheme-theoretic inertia.
* Arbitrary S, every characteristic, and arbitrary affine coordinate rings are
  allowed. All variables and the universe are explicitly bound;
  `set_option autoImplicit false` enforces this during compilation.

Searches (all through the prescribed wrapper, except the local rg/grep reads):

1. `leanfinder`, query `An etale cartesian stabilizer preserving map of finite
   locally free affine scheme groupoids induces an etale map of invariant
   spectra and a cartesian square`: OK, 8 hits, ordinary etale base-change,
   composition and cancellation lemmas and the etale category; no comparison.
2. `loogle`, query `"invariant", "etale"`: OK, 0 hits.
3. `grep`, query `groupoid.*invariant|invariant.*[eE]tale|[eE]tale.*invariant`:
   OK, 17 hits, all manifold local invariant properties; no scheme result.
4. `leansearch`, query `An etale morphism of affine groupoid schemes cartesian
   on source target and stabilizers gives an etale quotient map on invariant
   rings`: OK, 8 hits, ordinary etale definitions and permanence, plus a
   representation invariants-functor formula; no scheme-groupoid result.
5. `rg` of `lean/WeilConjectures` and `lean/Sheaf` with the same pattern and
   groupoid-morphism variants found the existing groupoid laws, integrality,
   orbit-fibre and basis-descent modules and stack consumers, but no statement
   of 0DT9. `grep -rn` for the exact item ID in `lean/WeilConjectures` found
   none. `rg` for invariant definitions found equalizer-based affine-relation
   invariants and finite-group action invariants. Neither states this theorem;
   the Mathlib equalizer is used directly, with no duplicate definition.

There is no statement correction and no `STATEMENT-DISPUTED` flag.
The initial server compile passed in sandbox and library modes (10.8 s and
5.4 s). The final file is also compiled with all explicit proof imports before
delivery. No direct Lean or Lake build is run.

## Second reading by Q66

Performed a separate in-process reading of the saved node statement, the complete
saved signature, the interpretation paragraphs, Stacks 0DT9, and Mathlib's
`IsPullback` definition and `isoPullback` projection identities. The dispatcher
explicitly prohibits starting other agents, so this is a second pass by this
worker; no independent agent review is claimed. The maintainer's independent
review remains the delivery review.

The clause table above was checked against the saved signature. In particular,
the two source/target squares have the correct ordering `b,s',s,a` and
`b,t',t,a`; their commutativity supplies the corresponding operation equations.
The all-scheme unique-loop-lifting hypothesis is equivalent to the third square,
including nonreduced inertia. The normalized φ is unique by subtype injectivity,
and q,q' are induced by the inclusions of the actual global-section equalizers.
The final square has ordering `a,q',q,Spec.map φ`, giving the stated canonical
comparison, rather than an unspecified isomorphism. The four affine hypotheses,
four finite-locally-free hypotheses, etaleness of a and all base compatibilities
are present. None of the empty or variable-rank cases is excluded. No mismatch
or correction was found; three direct imports for already stated proof inputs
were added before the final compile.
