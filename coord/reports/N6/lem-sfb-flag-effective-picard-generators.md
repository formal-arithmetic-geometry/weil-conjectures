## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.FlagEffectivePicardGenerators` states
`AlgebraicGeometry.flag_effective_picard_generators`, with its sole proof `sorry`.
It introduces no definitions, auxiliary assumptions, or new nodes. The original informal
statement and its six proof steps are preserved. Two already-landed definition nodes,
`def-sfb-borel-subgroup-scheme` and `def-sc-invertible-module`, are added to stmt_deps
because the statement uses their existing declarations.

Source read: Milne, Algebraic Groups (2017), printed p.392 (PDF page 404), the standing
paragraph before Lemma 18.21, its statement and entire proof. The standing split connected
group-variety hypotheses are automatic over algebraically closed F; reductivity is not
assumed. The latest blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
clause (3), was read for the surrounding supporting branch. The node is not a blueprint
unit's own statement.

Clause-by-clause rendering:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
- F-group schemes G and B: `G B : Over (Spec (.of F))`, each with `GrpObj`.
  These are internal group objects, including multiplication, inverse, unit and all laws.
- G smooth, connected, affine and finite type: `[Smooth G.hom]`,
  `[ConnectedSpace G.left]`, `[IsAffine G.left]`, `[LocallyOfFiniteType G.hom]` and
  `[QuasiCompact G.hom]`. The last two together mean finite type. B is a closed subgroup
  by the next hypothesis, so is automatically affine and finite type; neither property
  has been dropped by leaving out its redundant separate binder.
- Borel B contained in G: `i : B ⟶ G`, `hB : IsBorelGroupScheme i`.
  Reading Borel.lean and Semisimple.lean verifies that this includes closed-subgroup
  homomorphism, smoothness, nonempty connectedness, scheme-theoretic solvability and
  maximality among all such closed subgroups. Solvability terminates the actual derived
  subgroup series; it is not solvability of the group of rational points.
- Represented fppf quotient Q: `Q : Over (Spec (.of F))`, the displayed presheaf
  coequalizer, its arrow `ηQ` to `yoneda.obj Q`, and `hηQ`, bijectivity of precomposition
  into every Type-u fppf sheaf. The coequalizer identifies g with gb, so is the right-coset
  presheaf. Fppf subcanonicity makes the target representable a sheaf; the universal
  property identifies it with sheafification, not an arbitrary chosen quotient map.
  This is exactly the landed `borel_quotient_affine_cell` interface. The quotient
  morphism π mentioned in the prose is the morphism corresponding by Yoneda to the
  coequalizer projection followed by ηQ; it is unused in the conclusion and introduces
  no independent datum or hypothesis. Using the big over-site agrees with sheafifying
  on affine F-algebras because affine schemes form a basis for this topology.
- Nonnegative integer r and invertible modules L_1,...,L_r: `∃ (r : ℕ)
  (L : Fin r → Q.left.Modules) (hL : ∀ j, (L j).IsInvertible)`. Fin r simply numbers
  the same r objects starting at zero. `IsInvertible` is Zariski-local rank one.
- Every generator has nonzero global sections: `∀ j, ∃ s : Γ(L j, ⊤), s ≠ 0`.
  This is nonvanishing of global sections, not stalkwise nonvanishing of a section
  and not nonzeroness of the invertible module itself.
- Every Picard class is an integer combination: `∀ M : Q.left.Pic,
  ∃ a : Fin r → ℤ, M = ∏ j, (@Scheme.Pic.ofIsInvertible Q.left (L j) (hL j)) ^ (a j)`.
  The existing Picard group uses multiplicative notation: multiplication is tensor
  product, one is the structure-sheaf class, and inverse is the dual. Thus integer
  powers and product render precisely the integer linear combination in the node.
  All classes, not just effective classes or actual chosen representatives, are quantified.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field` (line 180).
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed` (lines 57–64), not an extra
  choice of algebraic closure.
- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj` (lines 41–48), with
  its specialization to `Over (Spec F)` documented in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs (module documentation).
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` (lines 36–47).
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType` (lines 38–46),
  and Morphisms.QuasiCompact: `QuasiCompact` (lines 40–46).
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth` (lines 59–65).
- Mathlib.Topology.Connected.Basic: `ConnectedSpace` (lines 703–708), including nonempty.
- Sheaf.AlgebraicGeometry.GroupScheme.Borel: `AlgebraicGeometry.IsBorelGroupScheme`;
  its complete definition at line 31 was read along with `IsDerivedGroupScheme`,
  `GroupSchemeDerivedLength`, and `IsSolvableGroupScheme` in GroupScheme.Semisimple.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (lines 58–68).
- WeilConjectures.AlgebraicGeometry.PicardFunctor: `AlgebraicGeometry.Scheme.Pic`
  (lines 158–169) and its isomorphism-class API (through line 205).
- WeilConjectures.AlgebraicGeometry.Picard.Group:
  `Scheme.Pic.ofIsInvertible` (lines 84–89), `instCommGroup`, `mulIso`, `oneIso`,
  and the definitions of multiplication and inverse (lines 107–158).

The module also imports the recorded proof prerequisites which have declarations:
`borel_quotient_affine_cell`, `regularLocalUFDBoundaryFactorization`,
`UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one`,
`NoetherianSpace.finite_irreducibleComponents`,
`AlgebraicSpace.regularSpaceDivisorLineDictionary`, and
`Scheme.Modules.nonempty_iso_unit_of_mvPolynomial_field`.
The stalk spreading proof prerequisite has no Lean record yet, so has no import;
its entire use is retained in proof step 3 in the theorem docstring.

Edge cases checked before writing:

- r=0 is allowed. Fin 0 has no elements, the section clause is vacuous and the
  empty product equals one, precisely triviality of Pic(Q).
- G=B, including the trivial group, has point quotient. The empty generator family
  satisfies the conclusion; no positive dimension, nontrivial group, or reductivity
  assumption appears.
- GL2/B gives the usual P1 case with an effective positive generator and arbitrary
  positive or negative integer powers; restricting to nonnegative powers would fail.
- Nonreductive G is included, as the source and the affine-cell dependency require.
- All characteristics are included. The group scheme and test-scheme definitions
  retain nonreduced test algebras. There is no characteristic-zero assumption.
- Nonzero global section is weaker than a nowhere-vanishing generator; the latter
  would incorrectly force every chosen generator to be trivial.
- The universe u is explicit throughout, with F and schemes in the same standard
  universe. The quotient sheaf tests use the same Type u as the published quotient
  interface. Pic(Q) lives in Type (u+1), with no illicit smallness restriction.

Searches actually run:

- `msearch.py ... leanfinder "The Picard group of a flag variety G/B is generated by
  finitely many line bundles with nonzero global sections"`: eight hits, all ring
  Picard-group constructions or triviality facts; none states this theorem.
- `msearch.py ... loogle '"Picard", "Borel"'`: zero hits.
- `msearch.py ... grep 'Picard.*[Ff]lag|[Ff]lag.*Picard|[Ee]ffective.*[Gg]enerator'`:
  zero hits.
- `msearch.py ... leansearch "Picard group of a Borel quotient is finitely generated
  by effective invertible sheaves"`: eight ring-Picard/invertible-module hits,
  none gives this theorem.
- Local rg searches for Borel, flag/Picard, IsBorelGroupScheme, IsInvertible and Picard
  definitions in lean/Sheaf, lean/WeilConjectures and Mathlib found and reused Borel.lean,
  BorelQuotientAffineCell.lean, Modules/Invertible.lean, PicardFunctor.lean and
  Picard/Group.lean. The node-id search and the proposed full declaration-name search
  in WeilConjectures, Sheaf, Mathlib and dag/lean_names_upstream.json found no existing
  declaration of the requested theorem. No search failure is recorded as a negative hit.

No statement dispute, source correction, new notion or dependency repair is needed.
The sole new theorem's proof is sorry. Its module and declaration docstrings contain
source and blueprint identifiers and all six steps of the node's proof.

Validation: scompile.py checked the sandbox module and the library-shaped module
successfully on the server (27.2 s and 8.6 s respectively), with no errors or warnings.
No direct library edit, direct git command, local compile or global build was run.

## Second reading by N6

This is the author's separate clause-by-clause rereading; the maintainer supplies the
independent review, as required by the dispatcher brief (no other agents were started).
Reopened the node, Milne printed p.392, and the final Lean file. Field, algebraic closure,
internal group objects, all five group geometry hypotheses, the Borel predicate and
represented fppf right-coset quotient match the node's hypotheses. Checked that the
quotient binders are identical to the already-landed affine-cell theorem, so stage 3
can apply that theorem directly. Read the Picard group definitions again to check the
multiplicative notation, integer exponents, unit and dual; the formula states generation
of every class. Read the invertibility predicate to check Zariski-local rank one.
Checked that the section clause says existence of a section unequal to zero, and that
r=0 has no hidden nonempty-instance requirement. No omitted or strengthened clause
was found. Added the already-landed Borel and invertible-module definition nodes to
stmt_deps to expose those notions explicitly; no statement or proof-plan change was made.
