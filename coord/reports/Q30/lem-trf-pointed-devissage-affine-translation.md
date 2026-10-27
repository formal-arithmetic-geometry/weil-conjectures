## Worker report

Item: `lem-trf-pointed-devissage-affine-translation`, group Q30, stage 2.

The module `Sheaf.TraceFormula.PointedDevissageAffineTranslation` states
`AlgebraicGeometry.PointedAffineDevissage.exists_affineSections`, with its sole proof
`sorry`. Its docstring gives the node's seven-step proof, including the flatness/localization
argument for primality and the actual generic-point residue-map comparison.

The helper `Entry` and recursive `entry` accessor unpack the existing chain; they do not
replace the dependency's notion. The three entry section functions are the actual presentation,
quotient, and standard-basis section maps. `IsAffineSections` spells out the comparison
required by the item's phrase "taking affine global sections". These are canonical-map and
comparison helpers belonging to this node, as permitted by the stage-2 helper rule; their
declarations are recorded in `lean.declarations`. All definitions have real bodies.

Hypothesis and clause correspondence:

- Commutative rings and the finite-type homomorphism: `R S : CommRingCat.{u}`,
  `[Algebra R S]`, `[Algebra.FiniteType R S]`; the map is `algebraMap R S`.
- The prime q and its inverse image p: `q : PrimeSpectrum S` and
  `Ideal.comap (algebraMap R S) q.asIdeal`. Primality of the inverse image is the
  existing Mathlib instance; p is determined by q rather than independently chosen.
- The finite S-module: `N : ModuleCat.{u} S` and `[Module.Finite S N]`.
- B, X, and the associated quasi-coherent module: `Spec R`, `Spec S`, and `tilde N`.
- The supplied pointed affine chain: the binder `c : PointedAffineDevissage (Spec R)
  (Spec.map (CommRingCat.ofHom (algebraMap R S))) (tilde N) q n` uses the recorded
  dependency, including its affineness, pointing, and generic-residue hypotheses.
- A complete algebra devissage of N/S/R over p: the conclusion's
  `D : CompleteAlgebraDevissage R S (Ideal.comap (algebraMap R S) q.asIdeal) N`.
  This retains every finite-presentation, surjectivity, finiteness, smoothness,
  geometric-irreducibility, initial/successive module, and final-zero clause of that definition.
- Same length: the `length : D.n = n` existential in `IsAffineSections`.
  Entry indices use `Fin.cast length`, preserving their numerical values and order.
- A_j, C_j = B_j, M_j are affine sections: the `coordinateA`, `coordinateB`, and
  `module` equivalences in `IsAffineSections` identify these respectively with
  `Γ(entry.datum.Z, ⊤)`, `Γ(entry.datum.Y, ⊤)`, and `Γ(entry.datum.G, ⊤)`.
  The first two conjuncts preserve the actual R-actions via `ΓSpecIso` and the base maps;
  the third makes the module equivalence semilinear for `coordinateA`.
- Affine sections of the ring maps: the fourth conjunct identifies `D.bToA` with
  `entry.datum.π.appTop`; the fifth identifies `D.sToA` with the first closed map's
  `appTop`, using `ΓSpecIso S`; the sixth identifies every `D.bToAnext` with the next
  closed map's `appTop`. These are diagram comparisons, rather than unspecified maps.
- Same ranks and the actual alpha maps: `rank : ∀ i, D.rIndex i = entry.rank` and
  the seventh conjunct. It equates the image under `D.alpha` of each standard basis
  vector `Pi.single k 1` with `entry.basisSection (Fin.cast (rank i) k)`. The latter
  evaluates the given sheaf alpha on its corresponding free basis section at the top open.
  Linearity determines the entire map, including rank zero.
- Affine sections of the module isomorphisms: the eighth conjunct compares `D.firstIso`
  with `entry.presentationSection` and `tilde.toOpen N ⊤`. The ninth compares `D.cokerIso`
  on every quotient class with the next presentation and the preceding actual
  `entry.quotientSection`. The latter is the section map of `cokernel.π entry.alpha`.
  Heterogeneous equalities accommodate the extracted entry's source scheme/module;
  they assert equality of the actual maps, not just the existence of an isomorphism.
- Primality and the residue-field isomorphism are `D.pPrime` and `D.residue_bijective`.
  Because the section alpha is retained, the residue condition concerns that map.
- The empty chain: `length` forces `D.n = 0` when `n = 0`; all index comparisons
  are then empty, and the dependency's `D.zero_case` records `Subsingleton N`.
- No support-dimension equality is added. The theorem uses exactly the supplied auxiliary
  chain; none of the comparison conjuncts mentions a support dimension.

Dependency declarations read and used:

- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`,
  and `Scheme.ΓSpecIso`.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `AlgebraicGeometry.tilde`,
  `tilde.toOpen`, and `tilde.toOpen_res`; the module's header fixes the common
  ring/module universe used here.
- `Sheaf.AlgebraicGeometry.PointedAffineDevissage`: `PointedAffineOneStep`,
  `PointedAffineDevissage`, and its `nil`/`cons` signatures, read in full.
- `Sheaf.TraceFormula.CompleteAlgebraDevissage`: `CompleteAlgebraDevissage`,
  including all its fields, read in full.

Statement-dependency modules are public imports. The recorded proof plan's available
modules are plain imports, including the closed-immersion and finite-presentation criteria,
finite/quasi-coherent pushforward and cokernel formulas, affine fibre products,
smoothness/flatness and torsion-freeness, residue localization, and function fields.
No dependency record needed repair; no node or statement was added or corrected.

Edge cases checked before and after writing: n = 0; a rank r_j = 0 (the basis family is empty
and the free source is the zero module); N = 0; arbitrary positive characteristic and
characteristic zero; nonreduced R such as k[e]/(e^2); a nonfield domain base such as Z.
The generic-fibre argument does not incorrectly assume R is a domain: it first passes to
R/p, and uses flatness to inject C_j/pC_j into the integral fibre ring. Empty initial schemes
or zero initial rings have no q, exactly as in the node. No support-dimension assumption or
independent universe of test objects was introduced. The section data use the existing
common-universe tilde and scheme-module interfaces.

Searches made with the prescribed `msearch.py Q30 <item>` wrapper:

- LeanFinder query: "Taking global sections of a pointed affine scheme devissage yields a
  complete algebra devissage with the same rings modules and basis maps". Result: eight
  hits, namely affine-basis-cover rings, affine schemes and their recursion, affine Spec,
  affine limit section vanishing, and affine-cover objects. None states this conversion.
- Loogle query: `AlgebraicGeometry.PointedAffineDevissage,
  AlgebraicGeometry.CompleteAlgebraDevissage`. Result: zero hits; the remote search index
  does not know the project-local first identifier. Local source searches below cover it.
- Mathlib grep query `devissage|Devissage` in `AlgebraicGeometry`: zero hits.
- LeanSearch query: "Affine global sections convert a complete devissage of quasicoherent
  modules to an algebra devissage". Result: eight hits for `AffineScheme.Γ`, `ΓSpecIso_inv`,
  `IsAffineOpen.isoSpec`, affine recursion/cases, and `Scheme.isoSpec`; no devissage theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for `devissage|Devissage` and the item's id,
  followed by the focused `PointedAffineDevissage|CompleteAlgebraDevissage|
  exists_affineSections|AffineSectionsIdentification` search in the relevant geometry and
  TraceFormula directories. Result: the two recorded notions and other consumers, plus
  unrelated affine-section comparisons; no existing conversion theorem or duplicate helper.
  The exact item-id search in upstream Lean found no declaration.

Source checked directly: `literature/stacks-project/flat.tex`, the full definition
`definition-complete-devissage-algebra` (05HX), and the full `remark-same-notion` (05I0).
The node accurately records the stated one-direction implication after dropping the
support-dimension conditions. No STATEMENT-DISPUTED issue was found.

Validation: the prescribed `scompile.py` compiled the module both as a sandbox and under
its actual library module name, cleanly, in 6.1 s and 5.2 s respectively. All variables and
universes are explicit, with `autoImplicit false`; every line is at most 100 characters.
The sole theorem proof remains `sorry`. Initial compiler failures were repaired: use of
a cokernel morphism's section projection, and expensive generated constructor lemmas for
a large comparison structure. The final comparison is the same explicit existential-and-
conjunction predicate, avoiding those generated lemmas without increasing compiler limits.

## Second reading by Q30

This is the dispatched worker's separate self-check with the node and final source open;
no other agent was started, as instructed. The maintainer's independent reading remains
part of delivery review. The check matched each hypothesis and clause as listed above,
and checked the dependency structures directly. In particular, it verified the direction
of `length` and both rank casts; R-linearity through both coordinate ring identifications;
all three kinds of ring map; alpha on the actual standard basis; the initial presentation
square using the tilde unit; and the successive square on every quotient class. It also
checked that the terminal-zero and residue-field clauses come from the existing complete
algebra devissage, rather than being silently omitted. The heterogeneous equalities compare
the next entry's input with the preceding chain cokernel, which the `cons` constructor fixes.
The check found no remaining statement mismatch and made no mathematical change.
