## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.DominantFlagLineKempfVanishing`
states `AlgebraicGeometry.dominant_flag_line_kempf_vanishing`. Its only theorem
has proof `by sorry`. It defines no notion, makes no statement correction and
changes only the item's `lean` record. There is no released repair note.

I read the item, every statement dependency and its recorded declaration and
source docstring, the statement/proof dependency records, the stage-2 contract,
and Milne's printed pp.479--480 (PDF pp.491--492). Milne 22.48 gives the
inverse-character quotient action. I retain the sign correction already present
in the reviewed node, rather than using the inconsistent literal sign of 22.51.
The proof docstring gives all six steps of the node, including Serre twisting,
Andersen--Haboush, the cohomological retract and characteristic-zero Kodaira.

Hypothesis and conclusion correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
  The universe is explicit and unrestricted; no characteristic binder is present.
- The F-group scheme is `S : Grp (Over (Spec (.of F)))`. The recorded
  `hS : IsSemisimpleGroupScheme S.X` means smooth, connected, affine, finite type,
  and no nontrivial smooth connected solvable normal closed subgroup. I opened
  `GroupScheme/Semisimple.lean`: its `IsSolvableGroupScheme` is termination of
  the scheme-theoretic commutator series, not abstract solvability on F-points.
- `hsc` is exactly the simply-connected condition from the rho dependency:
  every homomorphism `f : S' ⟶ S.X` from a semisimple group, with surjective
  underlying scheme map and finite kernel, is an isomorphism when that kernel
  commutes with all elements after every commutative F-algebra extension.
  `IsFinite (GrpObj.ker f).hom` is the finite-coordinate-algebra condition.
  These test algebras live in the field/scheme universe, rather than an
  independently smaller universe. Thus the centrality hypothesis is not vacuous.
- `T`, `B`, `iT`, `iB`, `j`, and `hTB : IsRhoBorelPair iT iB j` fix precisely
  the split maximal torus and Borel containing it. Unfolding the recorded
  definition gives maximality, an isomorphism with a finite product of G_m,
  `IsBorelGroupScheme iB.hom.hom`, and `j ≫ iB = iT`.
- The character lattice is the actual additive Hom group
  `Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))`, not an
  abstract lattice chosen separately. The two commutative-group-object witnesses
  are those supplied by the recorded reductive Borel-pair theorem.
- `Φ`, `P : RootDatum Φ ... ...`, and `b : P.Base` give the roots, coroots,
  perfect integer pairing, and simple-root base. `hroot` identifies the roots
  with the actual characters. `hpair` identifies the integer pairing with
  character/cocharacter composition and the integer power morphism on G_m.
  `hconjS`, `hconjB` fix the actual conjugation actions on tangent spaces;
  `hweights` says the roots are exactly their nonzero character weights on Lie(S),
  and `hpos` says the positive roots are exactly the weights occurring in Lie(B).
  `[P.IsReduced]` is the reducedness supplied by that same dependency. These are
  the identifications in the dependency conclusion, not extra restrictions on S.
- `ρ` is a character, with `hρ : 2 • ρ = sum of the positive roots`.
  The explicitly filtered finite sum uses `b.IsPos`. This is precisely the
  half-sum identity in the integral character lattice. It does not divide in F;
  the equality also has its intended meaning in characteristic 2.
- The node's dominant weight λ is named `lam` (λ is a Lean parser keyword).
  `hlam : ∀ α ∈ b.support, 0 ≤ P.toLinearMap lam (P.coroot α)` gives each of
  its simple-coroot inequalities, including zero pairings.
- The unipotent radical is `U` with inclusion `iU`, closedness `hUc`, normality
  `hUn`, smoothness `hUs`, connectedness `hUconn`, unipotence `hUu`, and the
  largest-subgroup property `hUmax`. Unipotence is the dependency's geometric
  matrix-unipotence predicate. The projection is `p : B ⟶ T`; `hp` fixes its
  restriction to T, `hker` fixes its kernel U, and `hsplit` is the multiplication
  isomorphism U × T → B. Thus it is precisely the Borel projection specified by
  the recorded semidirect-product conclusion, rather than an arbitrary map.
- `Q` and `π` give S/B as an F-scheme and its quotient map. `hQ`, `hQft`, `hQqc`
  are properness and finite type from the dependency; `hπf`, `hπs`, `hπi`, `hπt`
  are faithful flatness, right-invariance, and the right-torsor kernel-pair square.
  These specify the very quotient in the node. They are properties already
  supplied by its chosen quotient, not added assumptions on the input group.
- `L : AssociatedCharacterLineBundle.Presentation S B iB Q π (p ≫ (-lam).toMul)`
  is the existing associated homogeneous line bundle; its actual section sheaf
  is `L.L`. The presentation includes the fpqc quotient, its orbit relation,
  natural section-representing property, and the specified pullback trivialization.
  Its character is the negative of the extension of λ. Since the recorded
  presentation uses the inverse character as fibre multiplier, the right action
  is exactly `(g,z)b = (gb, λ(p(b)) z)` as required. I do not define another
  line bundle or identify it merely through its global sections. Invertibility
  and coherence follow for this presentation from the homogeneous-line theorem;
  neither is replaced with an arbitrary supplied sheaf or added as an assumption.
- `RingedSpace.moduleCohomology Q.left.toRingedSpace i` is the recorded right
  derived functor of global sections on Zariski O_Q-modules, computed by injective
  resolutions. `IsZero (... .obj L.L)` states that the cohomology module is zero.
  `∀ i : ℕ, 0 < i → ...` ranges over exactly all the positive integer degrees;
  positive integers are precisely the positive natural degrees of this API.
- No condition excludes zero weight, characteristic 2, or empty roots. Rank zero
  has an empty positive sum, empty simple-root inequalities and a trivial flag;
  it is included without a positive-rank or nonempty-root typeclass.

Dependency declarations used:

- Mathlib's `Field` (`Mathlib.Algebra.Field.Defs`), `IsAlgClosed`
  (`Mathlib.FieldTheory.IsAlgClosed.Basic`), and `CategoryTheory.GrpObj`/`Grp`
  (`Mathlib.CategoryTheory.Monoidal.Grp`), the recorded field/closure/group notions.
- `Sheaf.AlgebraicGeometry.RhoSectionModules`:
  `AlgebraicGeometry.IsRhoBorelPair` and the interface of
  `AlgebraicGeometry.exists_rho_section_modules` (same simply-connected binders).
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `AlgebraicGeometry.reductive_borel_pair_structure` and
  `AlgebraicGeometry.semisimpleGroupScheme_isReductive`. I use the actual
  quotient/radical/root-datum data of this statement with all their identifications.
- `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections`:
  `AlgebraicGeometry.exists_homogeneousLineBundle_sections`; its defining public
  dependency `Sheaf.AlgebraicGeometry.GroupScheme.AssociatedCharacterLineBundle`
  provides `AlgebraicGeometry.AssociatedCharacterLineBundle.Presentation` and `.L`.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`, which records
  `RingedSpace.moduleCohomology` from
  `WeilConjectures.Topology.RingedSpaceModuleCohomology` as H^i.

Proof-only imports are the already stated proof dependencies
`WeilConjectures.AlgebraicGeometry.Descent`,
`Sheaf.AlgebraicGeometry.GroupScheme.RhoRegularWeylOrbit`, and
`WeilConjectures.AlgebraicGeometry.CoherentSerreVanishing`.
The homogeneous-line, Borel-pair and cohomology dependencies are public imports
because they also supply the objects of the statement. At writing, the other
proof dependency nodes (strict-dominant ampleness, proper-field coherence,
Frobenius/rho pushforward, finite ideal-twist comparison, canonical character,
Kodaira) have no recorded declaration/module; they remain named in the proof
plan for the maintainer to add their imports when stated. None is needed to
form the present signature.

Edge cases checked mathematically before writing:

- For S = 1 and the empty root system, Q = Spec F, the line is trivial and all
  positive cohomology vanishes. The signature allows this case.
- For SL2 with the Borel-root convention of the node, a dominant integer n ≥ 0
  gives O(n) on P1. The chosen negative presentation character gives that sign;
  positive cohomology vanishes. The opposite sign would fail for n ≥ 2.
- For λ = 0, the conclusion is H^i(Q,O_Q) = 0; no strict dominance was imposed.
- Characteristic 2 is permitted, since the half-sum is an integral-character
  equality, not inversion of 2 in F. Characteristic zero and every prime positive
  characteristic share the same statement.
- Degree zero is not asserted to vanish: in the trivial-group case H^0 = F.

Searches for an existing statement, made with the required wrapper:

- `msearch.py ... leanfinder "Kempf vanishing higher cohomology dominant homogeneous
  line bundles on flag varieties"`: eight results on projective terms of group
  resolutions, group (co)homology and derived Ext. I read the returned signatures;
  none concerns dominant character line bundles or Zariski flag cohomology.
- `msearch.py ... loogle '"cohomology", "dominant"'`: zero results.
- `msearch.py ... grep 'Kempf|kempf|dominant.*cohomolog|flag.*vanish'`: zero results.
- `msearch.py ... leansearch "Dominant homogeneous line bundles on a flag variety
  have vanishing higher Zariski cohomology"`: eight results on dominant scheme
  morphisms and Proj vanishing ideals. Their returned signatures do not match.
- Direct `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for Kempf/kempf, dominant/cohomology and flag/vanish
  gave no matching declaration (one incidental prose occurrence of "flag" and
  "vanishes" in `SmoothUnipotentExtension` is unrelated). Searching the item ID
  in `lean/WeilConjectures` gave no result. I also searched existing root-datum
  consumers and read `RhoRegularWeylOrbit` for the actual root/base interface.

No statement fault or STATEMENT-DISPUTED issue was found. Every binder and universe
is explicit under `set_option autoImplicit false`. The single-file server compile
passed for both sandbox and library module, with no errors or unexpected warnings.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
