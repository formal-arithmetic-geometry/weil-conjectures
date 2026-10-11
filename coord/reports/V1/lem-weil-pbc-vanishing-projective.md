## Worker report

The module `Sheaf.AlgebraicGeometry.VanishingProjective` states
`AlgebraicGeometry.coherentFormalModule_kernel_twist_vanishing`, with proof `sorry`.
No definitions or extra nodes are needed. The repository and source checkout were read only;
all authored files are in this item's sandbox. No local compilation was performed.

Hypothesis and conclusion correspondence:

- A commutative Noetherian ring: `{A : Type u} [CommRing A] [IsNoetherianRing A]`.
- An arbitrary ideal I of A: `(I : Ideal A)`; no properness or completeness assumption on I.
- Proper f to Spec A: `(f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]`.
  Noetherianity of X follows via `isNoetherian_of_locallyOfFiniteType f`, supplied explicitly
  to the existing category rather than assumed as an additional hypothesis.
- An invertible module L: `(L : X.Modules) [L.IsInvertible]`.
- Absolute ampleness: `(hL : Scheme.Modules.IsAmple X L)`, precisely the landed
  Stacks 01PS definition; no field or relative projective hypothesis is added.
- The quasi-coherent ideal associated with I: `Scheme.IdealSheafData.ofIdealTop
  (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)`. This transports I to the
  global sections of Spec A and takes its associated ideal sheaf, the ideal version of tilde.
  Its extension is `.comap f`, the dependency's recorded definition of I O_X.
  Its packaged closed-subscheme description computes the same image ideal as tensor pullback;
  no second definition of pullback or of tilde is introduced.
- The system is `(F : @CoherentFormalModule X ... ( ... .comap f))`. Its underlying
  functor is `F.obj`; its levels are `F.obj.obj (op k) = F_(k+1)` and its transitions
  are `F.obj.map (homOfLE (Nat.le_succ k)).op`.
- The convention F_0 = 0 is rendered by the zero branch `F.obj.obj (op 0)`, using the canonical
  identification ker(F_1 → 0) ≅ F_1.
  At n = k+1, the other branch is the kernel of F_(k+2) → F_(k+1).
- The twist is `Scheme.Modules.tensorObj (...) (L.tensorPow d)`, the existing sheaf tensor and natural tensor power.
  The node defines d-fold tensor products, hence d is nonnegative; `d : ℕ` includes zero.
  The existential bound remains an integer `d₀ : ℤ` and the comparison is `d₀ ≤ (d : ℤ)`.
  A natural threshold would be equivalent, but the written integer threshold is retained.
- A single bound works for every n and d: `∃ d₀ : ℤ, ∀ (n d : ℕ), ...`.
- H^1 is `(RingedSpace.moduleCohomology X.toRingedSpace 1).obj ...` and its
  vanishing is `IsZero`, applied to the module object, not to its bare carrier.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, definition and FG equivalence.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, `Scheme.Modules.tensorPow`, and the existing tensor structure
  (imported through Ample).
- `Sheaf.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple`, its complete definition.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`: tensor product encoding was read;
  the scheme tensor structure already supplied through Invertible is used, with no private copy.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`: `Scheme.IdealSheafData.comap`.
- `Sheaf.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback` was read;
  the image ideal is already packaged by the recorded `comap`, so the signature has no
  standalone pullback term and needs no unused import of this module.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `tilde`, `tilde.toOpen`, `tilde.toOpen_res`
  were read; `ofIdealTop` is the existing ideal-sheaf specialization on the affine base.
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: `CoherentFormalModule`,
  `IsCoherentFormalModule`, including the coherence, annihilation and reduction conditions.
- `Sheaf.Paper.PQFCohomology`: `sheafCohomologyAndHigherDirectImages` was read;
  its stated cohomology is the established `RingedSpace.moduleCohomology` from
  `Sheaf.Topology.RingedSpaceModuleCohomology`, which is imported directly.

Edge cases: n=0 is included, with F_1, canonically the kernel of F_1 → 0; n=1 uses the first genuine
transition. d=0 uses the tensor unit and is covered when it satisfies the bound; no assertion
of untwisted vanishing is made without that inequality. I=0 permits a constant coherent
system, and the n=0 clause is ordinary ample-twist vanishing. I=A forces every level zero.
Zero systems, the empty scheme and the zero ring are not excluded. All objects have the
same arbitrary universe u as the established scheme/module encoding; no index universe
restriction or nonempty assumption is introduced.

Source checked: https://stacks.math.columbia.edu/tag/0884, Lemma 30.24.2, its full statement
and proof. The local `literature/stacks-project/coherent.tex` is absent on this machine, so the
original Stacks page was opened. The six-step proof in the docstring follows the node's
expanded proof, including its correction of the printed equality to a surjection.

Searches (real queries recorded by msearch.py in searches.jsonl):

- LeanSearch: `uniform first cohomology vanishing for kernels of a coherent adic inverse
  system twisted by large powers of an ample line bundle`: service unavailable (Internal
  Server Error), not evidence of absence.
- LeanFinder: `uniform first cohomology vanishing coherent formal modules ample tensor
  powers`: eight hits about group cohomology, sheaf cohomology of abelian sheaves and Tor;
  no matching uniform vanishing theorem.
- Mathlib grep: `vanishing.*projective|coherent.*formal|IsAmple`, AlgebraicGeometry:
  five projective-spectrum vanishing-ideal hits, no matching cohomology theorem.
- rg in WeilConjectures and lean/Sheaf for
  `vanishing_projective|vanishingProjective|lem-weil-pbc-vanishing-projective`:
  only a proof-docstring citation in GrothendieckExistenceProjective; no declaration.
- rg for ideal-sheaf constructors, tensorPow and moduleCohomology found the existing
  declarations used above, including the already-landed ideal transport pattern in
  FormalCompletionFullyFaithfulProper. No new notion or dependency module is required.

No statement correction and no STATEMENT-DISPUTED flag.

## Second reading by V1

I independently read the item node, its six proof steps, all ten statement-dependency
nodes, their recorded declarations, and the delivered Lean file. Verdict: the statement
is faithful; no Lean or node repair is needed. No new nodes or dependency modules occur
in this delivery, and there is no statement correction to review.

Source: the local Stacks .tex checkout is absent. I read the original `coherent.tex`
from https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex,
specifically `lemma-vanishing-projective` and the start of `section-existence`, and
checked https://stacks.math.columbia.edu/tag/0884. That section refers to the coherent
formal module definitions but imposes no blanket completeness assumption. Completeness
belongs to the preceding fully-faithful lemma, not this lemma. The source uses relative
ampleness; https://stacks.math.columbia.edu/tag/01VK establishes its equivalence with
absolute ampleness over an affine base. The formal system's hypotheses were also checked
at https://stacks.math.columbia.edu/tag/0EHN.

Object, hypothesis and conclusion inventory, with its Lean rendering and verdict:

1. A commutative Noetherian ring A: `{A : Type u} [CommRing A]
   [IsNoetherianRing A]`. I opened Mathlib Noetherian/Defs at the definition:
   this is Noetherianity of A as its own module, equivalently finite generation
   of every ideal. Exact; no domain, field or nonzero-ring assumption.
2. Any ideal I of A: `(I : Ideal A)`. Exact; no properness or adic completeness.
3. A scheme X and a proper morphism to Spec A: `{X : Scheme.{u}}
   (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]`. I opened Mathlib Proper:
   separated, universally closed and locally finite type. Universal closedness
   supplies quasi-compactness, so this agrees with the node's finite-type condition.
   Exact. `isNoetherian_of_locallyOfFiniteType f`, whose signature I opened in
   WeilConjectures/Mathlib/AlgebraicGeometry/Noetherian, obtains Noetherianity from
   these hypotheses and the affine Noetherian base; it adds no assumption.
4. An invertible O_X-module L: `(L : X.Modules) [L.IsInvertible]`.
   I opened the recorded Scheme.Modules.IsInvertible in the upstream Invertible
   module: local triviality on open neighbourhoods. This is rank-one local freeness;
   quasi-coherence follows locally from that of O_X. Exact.
5. Absolute ampleness of L: `(hL : Scheme.Modules.IsAmple X L)`. I read the
   landed Ample definition, including compactness and affine nonvanishing loci
   of positive tensor-power sections. It is precisely the node's 01PS notion;
   by 01VK it also renders the source's f-ampleness. Exact, with no closed-immersion
   or stronger very-ampleness hypothesis.
6. The associated affine ideal sheaf tilde I: `Scheme.IdealSheafData.ofIdealTop
   (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)`. I read ofIdealTop:
   on each affine open it maps the global ideal along restriction. ΓSpecIso.inv
   transports A to Γ(Spec A, O); the resulting ideal is the localization of I
   on principal opens. I also opened the recorded tilde, tilde.toOpen and
   tilde.toOpen_res. This is the ideal-sheaf specialization of the same associated
   sheaf, without defining another tilde. Exact.
7. Its extended ideal I O_X: the preceding term's `.comap f`. I opened the recorded
   IdealSheafData.comap: it is the kernel ideal of the base-changed closed immersion.
   Affine locally the base change is C/(IC), so its ideal is IC, exactly the image
   ideal in the node's tensor-pullback description. I opened the dependency's
   tensorPullbackObj and tensorPullback signatures: inverse image followed by
   change of rings. No competing pullback definition is used or required here.
8. An object (F_n) for n ≥ 1 of Coh(X,I O_X): `(F : @CoherentFormalModule X
   (isNoetherian_of_locallyOfFiniteType f) (...comap f))`. I opened
   IsCoherentFormalModule and CoherentFormalModule. Their three conditions are
   coherence of each level, annihilation by I^(k+1) at `op k`, and the reduction
   isomorphism F_(k+2)/I^(k+1)F_(k+2) ≅ F_(k+1) factoring the transition.
   Thus `F.obj` is the required inverse system, not an arbitrary functor. Exact.
9. Put F_0 = 0 and take every kernel K_n = ker(F_(n+1) → F_n):
   `match n with | 0 => F.obj.obj (op 0) | k + 1 =>
   kernel (F.obj.map (homOfLE (Nat.le_succ k)).op)`.
   In the positive branch the morphism goes from `op (k+1)` to `op k`, hence
   from F_(k+2) to F_(k+1), exactly K_(k+1). The zero branch is F_1,
   canonically ker(F_1 → 0). Exact up to this canonical isomorphism.
10. Twist by the d-fold tensor power: `Scheme.Modules.tensorObj ... (L.tensorPow d)`.
    I opened the upstream tensorObj and tensorPow, and the dependency's shared
    monoidal tensor/sheafification declarations. These are the sheaf tensor product,
    with tensorPow 0 the structure-module unit. Exact; no private tensor construction.
11. One integer bound independent of both indices: `∃ d₀ : ℤ, ∀ (n d : ℕ),
    d₀ ≤ (d : ℤ) → ...`. Quantifier order is exact: d₀ is outside n and d.
    The node describes d-fold tensor products, so natural d is appropriate. Even
    reading Stacks with integer tensor powers gives the equivalent eventual
    statement: a bound can always be increased to max(d₀,0), when no negative
    exponent is tested. No asymptotic case is lost.
12. First sheaf cohomology vanishes: `IsZero
    ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj ...)`.
    I read both PQFCohomology's signature and RingedSpaceModuleCohomology:
    this is R^1 of module global sections, valued in modules over Γ(X,O_X).
    IsZero of that module object means the zero cohomology module. Exact;
    it is neither the abelian-sheaf Ext encoding nor IsZero of a bare Type.

Edge cases: n=0 is explicitly included and n=1 uses F_2 → F_1, with no indexing
shift. d=0 is tested precisely when the integer bound allows it; no unwarranted
untwisted vanishing is asserted. I=0 gives isomorphic transitions and leaves the
F_1 case; I=A forces all levels to be zero. Zero systems, empty X, and the zero
ring are permitted. No characteristic hypothesis occurs. The source's fixed
positive integer index has no empty-index variant; no artificial nonempty index
assumption is introduced. The arbitrary universe u is explicitly bound, and
rings, schemes and module categories use the established shared encoding; objects
in distinct smaller universes can be placed in a common larger universe. There is
no independent small test-object universe making a geometric hypothesis vacuous.

Independent duplicate searches (different phrases from the worker's queries):

- `msearch.py ... leansearch "Uniform Serre vanishing for an adic system of coherent
  modules on a proper scheme"`: service returned Internal Server Error, recorded
  unavailable; this is not evidence of absence.
- `msearch.py ... leanfinder "Serre vanishing uniformly for successive kernels of
  adic coherent sheaves over a proper scheme"`: eight hits about affine limits and
  ring local cohomology; none gives the uniform system theorem.
- `msearch.py ... grep "kernel.*vanish|[Ss]erre.*vanish|[Ff]ormalModule"`:
  only two general kernel/cokernel comments in Mathlib, no matching theorem.
- Direct rg on both WeilConjectures and repository lean/Sheaf for kernel/twist,
  kernel/vanish, Serre/vanish, the Stacks label and the proposed declaration name;
  also read the Serre entries of dag/lean_names_upstream.json. I opened the nearby
  upstream `Scheme.Modules.exists_subsingleton_H_tensorObj_tensorPow`: it concerns
  one coherent module over a field and cannot supply a bound uniform in the levels
  of an adic system over a ring. I opened landed CoherentSerreVanishing and
  RelativeSerreVanishing: they likewise concern a single coherent module, not the
  successive kernels uniformly. GrothendieckExistenceProjective only cites this
  item in its proof docstring. No exact existing declaration was found.

H5/H6/H8/H9 checks: the delivered module has no definitions, only the named theorem
with proof `sorry`. Its module and declaration docstrings give Stacks 0884 and the
blueprint id. The declaration's six proof paragraphs match the node's six steps,
including the graded-algebra surjection in place of the printed equality and the
retraction argument for each summand. All imports are used for the proper morphism,
ideal extension, derived Noetherian instance, ample module, formal system and module
cohomology. No private declaration, local notation, local instance, hidden let/show
binder, unbound variable or unbound universe occurs. All lines are ≤100 characters.
The node's lean.statement equals the file's signature verbatim (checked by extraction).

Mismatches found and repairs: none. The Lean and node copy are retained as written;
this second-reading section and independent search records are the additions.
Validation: `scompile.py V1 lem-weil-pbc-vanishing-projective` on the delivered file
returned exit 0, compiled in 2.0 seconds, with no errors or warnings.
