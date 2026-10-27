## Worker report

The new module `Sheaf.AlgebraicGeometry.GroupScheme.RankOneFrobeniusExtension`
states `AlgebraicGeometry.rankOne_frobenius_extension`, with its entire proof
postponed by `sorry`. It introduces no definitions or additional nodes. The item
node changes only in `lean`; its mathematical statement and dependencies are unchanged.

Source read directly: Milne, *Algebraic Groups* (2017), printed pp.488--490,
especially Proposition 23.14 and paragraph 23.16; formula (146), pp.485--486,
is also the source of the scalar-times-Frobenius conclusion. The node's explicit
SL2 semidirect-quotient proof is retained step by step in the theorem docstring.

The finite indexing family packages two independent groups: index 1 is H_1 and
index 0 is H_0. Boolean true means the displayed positive root, false its negative.
Here is the correspondence for every hypothesis and clause:

| Node clause | Lean rendering |
| --- | --- |
| Algebraically closed field F | `{F : Type u} [Field F] [IsAlgClosed F]` |
| Characteristic exponent p, including p=1 in characteristic zero | `(p e : ℕ) [ExpChar F p]`; Mathlib's `ExpChar.zero` has p=1, and `ExpChar.prime` has prime positive characteristic |
| q=p^e with e nonnegative | Every occurrence of q is literally `p ^ e`; `e : ℕ` includes zero |
| Affine split reductive F-group schemes H_i | `H : Fin 2 → Grp (Over (Spec (.of F)))` and `hH`; the recorded `IsReductive` includes the affine finite-type algebraic group, smoothness, geometric connectedness and reductivity conditions |
| Split maximal tori T_i contained in H_i | `T`, `iT`, `hT`, `hsplit`; each split rank is separately existential and unrestricted |
| Characters and cocharacters have the dependency's meaning | The two lattices in `D` are exactly `Additive (T i ⟶ Grp.mk Gm)` and `Additive (Grp.mk Gm ⟶ T i)`; no auxiliary lattice replaces them |
| The canonical integral root pairing | `hpair` identifies composition of every character and cocharacter with the integer power morphism |
| Root data are reduced and roots are actual characters | `D`, `hred`, `hroot`; commutative group-object witnesses expose the pointwise abelian Hom group laws |
| Roots are adjoint character weights | `aH`, `hconj` pin the action to conjugation along `iT`; `hweights` says that the roots are exactly the nonzero characters with nonzero `TorusCharacterTangent.weightSpace` |
| Root sets are exactly {alpha,-alpha} and {beta,-beta} | `α : ∀ i, Φ i` selects an actual root; `hrank` gives the two-element description by a membership equivalence, with no hidden ambient roots |
| The coroot is the canonical geometric coroot | `hreflection` specifies the normalizer representative acting by `t ↦ t * α∨(α(t))⁻¹`; the cocharacter is exactly `((D i).coroot (α i)).toMul`, not an arbitrary cocharacter with pairing two |
| Root subgroups have the dependency's meaning | `U`, `j`, `hU`: closed, smooth, connected, torus-stable, with differential image the selected positive or negative root weight space; `hparameter` gives isomorphism with the existing additive group |
| h:T_1→T_0 | `(h : T 1 ⟶ T 0)`, a morphism of bundled group objects |
| h* is character pullback | `hstar`, with `hhstar` fixing its value on every character to composition with h |
| Pullback is injective with finite cokernel | `hinj`, `hfinite : Finite (_ ⧸ hstar.range)`; this is the abelian group cokernel |
| h*(beta)=q alpha | `hα : hstar (α 0).val = (p ^ e) • (α 1).val` |
| h∘alpha∨=beta∨∘(t↦t^q) | `hcoroot`, an equality of actual morphisms over F, using the power of the identity of Gm |
| There is a group-scheme homomorphism f | Existential `f : H 1 ⟶ H 0` |
| f restricts to h | `iT 1 ≫ f = h ≫ iT 0` |
| f maps each root subgroup onto its corresponding target subgroup | Existential `fU`, factorization `j 1 ε ≫ f = fU ε ≫ j 0 ε`, and `Surjective (fU ε).hom.hom.left` |
| For any chosen four root parametrizations | `∀ x : ∀ i ε, Grp.mk Ga ≅ U i ε`, after choosing the same f and fU |
| Constants c_+,c_- lie in F units | `∃ c : Bool → Fˣ`, before all algebra and parameter quantifiers |
| Formula holds for every commutative F-algebra A and a∈A, both signs | `∀ (ε : Bool) (A : Type u) [CommRing A] [Algebra F A] (a : A)` and the displayed equality of A-points, with `algebraMap F A (c ε : F) * a ^ (p ^ e)` |
| Arbitrary torus dimension and characteristic two | No rank-one assumption on T, no restriction on its central dimension, and no exclusion of p=2 |

The normalizer formula is an explicit reading of *the geometric coroot of the
root datum*, not an extra restriction on the groups in the source. Over an
algebraically closed field a Weyl reflection has a rational normalizer
representative. With the pairing fixed by composition, the character formula
`s_α(χ)=χ-<χ,α∨>α` is equivalent to the formula on t in `hreflection`.
Conversely a normalizer reflection with that formula identifies the canonical
coroot: on the rank-one derived torus it is the usual reflection, and on the
connected center it is the identity. Characters separate torus morphisms, so a
central shift of the coroot would change this reflection and is excluded.
This matters for the arbitrary-dimensional central tori expressly allowed by
the node. Abstract `RootDatum` axioms alone would not enforce that geometric
identification; no such arbitrary abstract datum is substituted for the node's
canonical one.

The subgroup characterization uses exactly the recorded root-parametrization
theorem's uniqueness specification: any two smooth connected closed stable
subgroups with the same tangent weight space are uniquely isomorphic over H.
The existing Ga model has its prescribed addition group law and the parameter
point is the recorded `TorusCharacterTangent.additiveParameterPoint`, given by
polynomial substitution. There is no arbitrary map used in its place.

Dependencies read and used:

- `def-weil-field`: Mathlib `Field`, source `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: Mathlib `IsAlgClosed`, source
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, as identified by the node's match.
- `def-sc-group-scheme`: Mathlib `CategoryTheory.GrpObj`, `CategoryTheory.Grp`
  and their bundled homomorphisms, with the specialization to `Over (Spec F)`
  documented in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `lem-sfb-reductive-borel-pair-structure`: public import
  `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`, declaration
  `AlgebraicGeometry.reductive_borel_pair_structure`; its full signature and
  docstring were read. Its actual character/cocharacter root-datum encoding,
  composition pairing, and adjoint-character weights are used here. Its
  predicates come from `ReductiveTorusCentralizer.IsReductive`,
  `ReductiveTorusCentralizer.IsMaximalTorus`, and `MultiplicativeType.splitTorus`.
- `lem-sfb-reductive-root-subgroup-parametrizations`: public import
  `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations`,
  declaration `AlgebraicGeometry.TorusCharacterTangent.reductive_root_subgroup_parametrizations`;
  its full signature, uniqueness clause, and docstring were read. Its
  `TorusCharacterTangent.IsStable`, `weightSpace`, and `additiveParameterPoint`
  supply the root subgroup and all-algebra parameter conventions.
- Mathlib `ExpChar` is read in `Mathlib.Algebra.CharP.Defs`, exposed by the
  explicit import `Mathlib.Algebra.CharP.Lemmas`; quotient group notation is
  exposed by `Mathlib.GroupTheory.QuotientGroup.Basic`.

All three proof-dependency nodes were read. Their Lean records are absent, so
there are no published proof-dependency modules to import:
`lem-sfb-opposite-root-sl2-parametrizations`,
`lem-sfb-rank-one-semidirect-presentation`, and
`lem-sfb-faithfully-flat-group-quotient-universal`.
They remain in the node's proof dependencies and theorem proof docstring.
No missing statement prerequisite was found and no dependency copy was needed.

Edge cases checked mathematically before writing and on the second reading:

- p=1 and e=0 both give q=1. Neither the constant units nor either root group
  degenerates, and no division by p or e occurs in the signature.
- p=2 is permitted. Root and coroot information lives in integral character
  lattices, not differentiated characters; alpha and minus alpha remain
  distinct even though their differentials can coincide in characteristic two.
- SL2, PGL2 in characteristic two, GL2, and products with arbitrary split
  central tori fit the hypotheses. A root set with an actual chosen alpha
  excludes a purely toric/empty-root group exactly as the node does; rank-zero
  maximal tori do not become a spurious case of this rank-one assertion.
- Nonreduced test algebras and the zero algebra are included by `[CommRing A]`;
  neither domains nor reducedness nor nontriviality is imposed on A.
- For A=F[t] and q>1, the qth-power map need not be onto A. The conclusion
  therefore asserts surjectivity of the underlying root subgroup *schemes*,
  exactly as the node's proof requires, and never pointwise surjectivity for A.
- The same F-universe is used for the schemes and their test algebras, as in
  the recorded dependencies; this includes coordinate algebras and dual-number
  algebras and introduces no independent smaller universe or size equality.
- The quantifier over parametrizations comes after f, so f is uniform across
  all choices; the units come before A, so constants are independent of A.

Searches for existing statements (2026-10-24):

- `msearch.py ... leansearch "Homomorphism of reductive group schemes extending
  a torus homomorphism with roots and coroots multiplied by a power of the
  characteristic"`: eight hits, including
  `RootPairing.smul_coroot_eq_of_root_eq_smul`, `RootPairing.Hom.ext_iff`, and
  `RootPairing.restrictScalars_coe_coroot`; no geometric extension result.
- `msearch.py ... leanfinder "A homomorphism of split maximal tori in reductive
  groups with roots plus and minus alpha extends when roots and coroots agree
  up to a Frobenius power"`: eight hits on abstract root pairings and their
  morphism extensionality, none giving the group-scheme extension.
- `msearch.py ... loogle "RootDatum, CharExp, MonoidHom"`: zero hits, unknown
  identifier `CharExp`. Reading Mathlib revealed that the correct name is
  `ExpChar`; the statement uses that existing class. A follow-up
  `msearch.py ... loogle "ExpChar"` returned twelve exact matches, including
  `ExpChar`, its zero/prime constructors and positivity and uniqueness lemmas.
- `msearch.py ... grep "Frobenius|isogen|root.*datum"
  LinearAlgebra/RootSystem`: six hits on the `RootDatum` terminology and the
  isogeny TODO in `Hom.lean`. Full `RootPairing.Hom` signature read: it is
  an abstract morphism preserving roots without Frobenius exponents and does
  not assert existence of a morphism of reductive group schemes.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `frobenius.extension|frobeniusExtension|rank_one_frobenius|rankOneFrobenius`:
  no existing statement. `grep -rn` for the item id in
  `lean/WeilConjectures`: no hit. Broader `Frobenius|frobenius|isogeny|Isogeny`
  search in both group-scheme directories found general `IsIsogeny`, reduced
  subgroup constructions, and other compatible-root/central-isogeny results,
  but no extension satisfying this statement. The compatible graph and
  central-isogeny declarations were opened to check their actual interfaces.

Compilation: the initial compile found only a precedence error in composing
the qth-power morphism with the target coroot; parentheses around the entire
power fixed it. `scompile.py Q05 lem-sfb-rank-one-frobenius-extension` then
compiled this file in sandbox mode (2.2 seconds) and its actual library module
mode (2.1 seconds), both clean, with no unexpected warning. The only postponed
proof is the named theorem itself. No statement fault or dispute was found.

## Second reading by Q05

The dispatcher explicitly forbids starting another agent; this is a separate
self-review pass, not a claim of an independent second worker. The maintainer's
independent delivery review remains applicable.

I reopened the item node, its two structural dependency signatures and the
new module. The table above matches each hypothesis and conclusion, including
three easily missed points: q is a characteristic-exponent power rather than
an arbitrary positive integer; the coroot is canonical geometrically even with
central torus directions; and the root maps are surjective schemes, with no
claim about surjectivity on every A-points group. I checked both sign branches,
source/target order in `hα` and `hcoroot`, the direction of the factorization
through fU, and the scalar embedding into A. The extension is chosen before
all parametrizations, and constants before test algebras. No clause was lost
or strengthened. No change to the accepted mathematical node was needed.

Delivery validation: `deliver2.py Q05 lem-sfb-rank-one-frobenius-extension --no-push`
printed `OK (dry run): commit 06cf867e737 passes the preflight and compiles; nothing pushed`.
The staged packet contains exactly the module, the item node and this report.
