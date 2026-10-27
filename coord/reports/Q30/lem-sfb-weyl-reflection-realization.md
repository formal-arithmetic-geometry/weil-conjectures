## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.WeylReflectionRealization` states
`AlgebraicGeometry.weyl_reflection_realization`, with a single `sorry` proof and no
definitions. The natural-language statement and proof are unchanged. The existing
`def-sfb-rank-one-root-interfaces` is added to `stmt_deps` because the signature uses
its actual normalizer quotient. No new nodes or dependency repairs are needed.

Hypotheses, in order:

- Algebraically closed field: `{F : Type u} [Field F] [IsAlgClosed F]`.
- Group schemes: `G T B : Grp (Over (Spec (.of F)))` uses the recorded `GrpObj`
  terminology via Mathlib's bundled group objects.
- Smooth, connected, affine, finite-type, reductive G: `hG :
  ReductiveTorusCentralizer.IsReductive G`. Its definition includes the algebraic
  group conditions, geometric connectedness and the absence of nontrivial smooth
  connected normal unipotent subgroups after algebraic closure.
- Split maximal torus inclusion: `iT`, `hT : IsMaximalTorus iT`, and `hsplit`.
- Borel containing T: `iB`, `hB : IsBorelGroupScheme iB.hom.hom`, and `j`, `hj`.
- Character and cocharacter lattices are exactly the additive actual group-scheme
  Hom groups from the Borel-pair theorem, not replacement abstract modules. The two
  commutativity instances expose the pointwise commutative Hom group structures.
- The specified Borel-pair root datum is `Φ`, `P`, `b`, and `[P.IsReduced]`.
  `hroot` identifies each root with its actual character. `hpair` identifies its
  perfect integer pairing with composition of character and cocharacter, as an
  integer power map. Perfectness and reflection axioms are fields of `RootDatum`.
- The actual adjoint actions are `aG`, `aB`, pinned to conjugation by `hconjG` and
  `hconjB`. `hweights` says the roots are exactly the nonzero character weights
  in Lie(G). `hpos` identifies the base's positive system with the Lie(B) weights.
  These are precisely the supplied data “as in” the recorded Borel-pair theorem.
- `E` is a rational submodule of the actual rationalized character lattice.
  `hE` identifies it with the rational span of all roots. It is not a freely chosen
  representation or a spanning assumption on the full character lattice.

Conclusions, clause by clause:

- W is the existing `RankOneRoots.Weyl iT`, namely the scalar-extension normalizer
  modulo its torus-point image. `Finite (RankOneRoots.Weyl iT)` is finiteness.
- `act` is an action on the torus. The first conjunct pins its value on every
  representative `n` to conjugation `t ↦ ntn⁻¹` after every algebra extension.
  This prevents choosing an arbitrary torus action.
- `ract` is the rational character action. Its pure-tensor equation uses
  `(act w).inv ≫ χ.toMul`, which is exactly `χ(n⁻¹tn)`; quantification over all
  q and χ uniquely specifies the rational extension.
- `r : W →* (E ≃ₗ[ℚ] E)` is the restriction: `(r w x).val = ract w x.val` for
  every x in E. `Function.Injective r` is precisely its faithfulness.
- `root : Φ → E` is pinned by `(root α).val = 1 ⊗ P.root α`. It introduces no
  choice of root vectors; the subtype inclusion is injective.
- `s : Φ → (E ≃ₗ[ℚ] E)` is pinned by
  `s α (root β) = root β - (P.toLinearMap (P.root β) (P.coroot α) : ℚ) • root α`.
  Since these vectors span E by hE, this equation is exactly the reflection
  `x ↦ x - ⟨x,α∨⟩α` on every x: two rational linear maps agreeing on the spanning
  roots agree on E, and the pairing extends rationally. No extra reflection data
  is assumed. Existence and invertibility are asserted by the theorem.
- `r.range = Subgroup.closure (Set.range s)` is precisely the asserted image
  subgroup, hence together with injectivity identifies W with the reflection group.
- The `Set.image` equality on `Φ` says the character action permutes all roots.
- `Φ = ∅ → E = ⊥ ∧ (∀ w, w = 1) ∧ Subgroup.closure (Set.range s) = ⊥`
  explicitly includes both trivial groups in the empty-root case.

Dependency declarations read and used:

- Mathlib `Field` (`Algebra.Field.Defs`), `IsAlgClosed`
  (`FieldTheory.IsAlgClosed.Basic`), and `CategoryTheory.GrpObj`
  (`CategoryTheory.Monoidal.Grp`); group-scheme interpretation also read in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `AlgebraicGeometry.reductive_borel_pair_structure`; its exact character/cocharacter
  RootDatum, conjugation and weight interface is reused in the binders.
- `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces`:
  `AlgebraicGeometry.RankOneRoots.normalizer`, `torusInNormalizer`, and `Weyl`.
  Their defining module and the entire definition node were read. The normalizer
  tests all algebras, so the definition retains subgroup-scheme normalization.
- The original Borel-pair import supplies its recorded predicates
  `ReductiveTorusCentralizer.IsReductive`, `IsMaximalTorus`, and `IsBorelGroupScheme`;
  their definitions and the actual weight-space declaration were inspected.
- The stated proof dependencies are imported without `public`:
  `RankOneRoots.reductive_rankOne_reflections`,
  `TorusCharacterTangent.reductive_root_subgroup_parametrizations`,
  `borel_root_product_coordinates`, `borelGroupScheme_normalizer_iff`, and
  `ReductiveTorusCentralizer.reductive_torus_self_centralizer` in their recorded
  modules. Their full signatures and docstrings were read. The root chamber
  simple-transitivity node has no Lean record yet, so it has no module to import.
  Its role is retained in the complete proof-plan docstring.

Searches:

- `msearch.py ... leanfinder` with “The normalizer quotient of a maximal torus in a
  reductive algebraic group acts faithfully on the rational root span with image
  generated by root reflections” returned eight abstract RootPairing hits,
  including `weylGroup`, `range_weylGroup_weightHom`, `range_weylGroupToPerm`, and
  `weylGroupRootRep`. They do not identify the geometric normalizer quotient.
- `msearch.py ... loogle 'RootPairing.weylGroup, RootPairing.reflection'` returned
  `range_weylGroup_weightHom` and `isSimpleModule_weylGroupRootRep_iff`; neither is
  the algebraic-group result. Mathlib's actual Weyl-group source was read.
- `msearch.py ... grep 'normalizer|weylGroup|reflection' LinearAlgebra/RootSystem`
  returned 25 hits about abstract root systems, not the geometric realization.
- `rg` searched `lean/WeilConjectures` and `lean/Sheaf` for Weyl, normalizer,
  rootSpan, rational character spans and the item id. The recorded rank-one
  definitions and theorem, Borel-pair theorem, and `RhoRegularWeylOrbit` were found;
  none states injectivity and image equality on E. The latter module supplies the
  same canonical full-action interface, which this statement follows.
- `tools/blueprint_refs.py search weyl-reflection-realization` found no imported
  blueprint unit with that name. This is a supporting lemma, not a unit statement.

Source check: opened the local Milne PDF (PDF pp.447--448 = printed pp.435--436).
Theorem 21.37 generates the geometric Weyl group by root reflections; its proof
uses the character action and chambers, and Corollary 21.38 gives the canonical
isomorphism. Printed pp.424--425 also give the precise inverse-conjugation
character formula. No statement correction or disputed assertion is required.

Edge cases: empty Φ gives E = 0 and both groups trivial, explicitly; central torus
factors are retained because E need not be the whole character space; rank one
has the expected two-root reflection. There is no characteristic restriction,
and all characters are group-scheme characters rather than differentials.
The arbitrary universe u is shared with the group schemes and test algebras, so
no lower test-algebra universe or extra universe equality has been imposed.

Validation: `scompile.py Q30 lem-sfb-weyl-reflection-realization` compiled the
sandbox and final library module cleanly (3.0 s and 2.9 s). The initial invalid
Mathlib import path and a parenthesis typo were repaired. Maximum line length is
90. The file uses `set_option autoImplicit false` and explicitly binds universe u.

## Second reading by Q30

This is a self-check; no second agent was started, as the dispatcher forbids it.
The maintainer's independent review remains required. Re-read the node and final
signature together: field and reductivity, split maximal torus, containing Borel,
actual character/root/coroot data, canonical inverse-conjugation action, rational
span restriction, finiteness, injectivity, generated image, root permutation and
empty-root triviality each have the clauses listed above. In particular the
reflection equation on roots determines its values on all E by hE, and the full
rational-action equation determines values beyond E. No hypothesis supplies the
conclusion in advance. No mathematical mismatch or correction was found.
