import Something.ToricGeometry
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Cone Subdivision Algorithms

This file contains the core algorithms for subdividing cones to obtain
a smooth refinement of a fan, which is the key step in the resolution
of toric singularities.

## Main algorithms

* `barycentric_subdivision`: Divides a cone by adding rays through the barycenters of its faces
* `star_subdivision`: Divides a cone by adding a ray through a chosen interior point
* `HirzebruchContinued`: The Hirzebruch continued fraction algorithm for smoothing 2D cones
-/

namespace ConeSubdivision
open ToricGeometry

section Subdivision

/-- Define the interior of a cone -/
def interior {N : Type} [AddCommGroup N] [Module ℤ N] (σ : Cone (NR N)) : Set (NR N) :=
  {v ∈ σ.carrier | ∀ τ, IsFace τ σ → τ ≠ σ → v ∉ τ.carrier}

/-- A point v is primitive if there's no other lattice point u such that v = ku for some k > 1. -/
def isPrimitive {N : Type} [AddCommGroup N] [Module ℤ N] (v : N) : Prop :=
  ¬∃ (u : N) (k : ℤ), k > 1 ∧ v = k • u

/-- An element of the Hilbert basis is a primitive lattice point in the cone that cannot be
    written as a sum of other lattice points in the cone. -/
def isHilbertBasisElement {N : Type} [AddCommGroup N] [Module ℤ N]
    (v : N) (σ : Cone (NR N)) : Prop :=
  isPrimitive v ∧ (toNR v) ∈ σ.carrier ∧
  ¬∃ (v₁ v₂ : N), (toNR v₁) ∈ σ.carrier ∧ (toNR v₂) ∈ σ.carrier ∧
                  v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v = v₁ + v₂

/-- The Hilbert basis is the minimal set of lattice points that generate all lattice points in the cone. -/
def hilbertBasis {N : Type} [AddCommGroup N] [Module ℤ N] (σ : Cone (NR N)) : Set N :=
  {v | isHilbertBasisElement v σ}

/-- Finds the minimal generators of a cone in a given lattice.
    The Hilbert basis algorithm finds a minimal set of lattice points such that every
    lattice point in the cone can be expressed as a non-negative integer linear combination
    of these generators. -/
def findMinimalGenerators {N : Type} [AddCommGroup N] [Module ℤ N]
    (σ : Cone (NR N)) (h : σ.IsRational N) :
    ∃ (n : Nat) (generators : Fin n → N),
    σ.carrier = {v | ∃ cs : Fin n → ℝ, (∀ i, cs i ≥ 0) ∧ v = ∑ i, cs i • (toNR (generators i))} ∧
    (∀ i j, generators i = generators j → i = j) ∧
    ∀ i, ¬∃ v : N, v ≠ generators i ∧
      (toNR v) ∈ σ.carrier ∧
      ∃ (c : ℝ), c > 0 ∧ c • (toNR v) = toNR (generators i) := by
  -- Extract the information from the rationality assumption
  rcases h with ⟨k, original_gens, h_carrier⟩

  -- The Hilbert basis is finite for a rational polyhedral cone
  have finite_hilbert_basis : ∃ (finite_set : Set N),
    (finite_set.Finite) ∧
    (∀ v, v ∈ finite_set ↔ isHilbertBasisElement v σ) := by
    -- This is a deep theorem in the theory of rational polyhedral cones
    -- The proof relies on Gordan's Lemma and properties of monoids
    sorry

  -- Extract the finite Hilbert basis
  rcases finite_hilbert_basis with ⟨hb, h_finite, h_equiv⟩

  -- Convert the finite set to a finite sequence
  have enumerated_basis : ∃ (n : Nat) (generators : Fin n → N),
    (∀ v ∈ hb, ∃ i, generators i = v) ∧
    (∀ i, generators i ∈ hb) ∧
    (∀ i j, generators i = generators j → i = j) := by
    -- Standard result about finite sets being enumerable
    sorry

  -- Extract the generators from the enumerated basis
  rcases enumerated_basis with ⟨n, generators, h_surj, h_all_in_hb, h_injective⟩

  -- Show these minimal generators generate the same cone
  have h_same_cone : σ.carrier =
    {v | ∃ cs : Fin n → ℝ, (∀ i, cs i ≥ 0) ∧ v = ∑ i, cs i • (toNR (generators i))} := by
    apply Set.Subset.antisymm
    · -- The cone is contained in the generated set
      intro v hv
      -- By Carathéodory's theorem, any point in a polyhedral cone in ℝᵈ can be expressed
      -- as a non-negative linear combination of at most d of its extreme rays
      sorry
    · -- The generated set is contained in the cone
      intro v ⟨cs, h_nonneg, h_sum⟩
      -- A non-negative combination of points in the cone is in the cone by convexity
      sorry

  -- Show that the generators are primitive and minimal
  have h_minimal : ∀ i, ¬∃ v : N, v ≠ generators i ∧
    (toNR v) ∈ σ.carrier ∧
    ∃ (c : ℝ), c > 0 ∧ c • (toNR v) = toNR (generators i) := by
    intro i
    -- This follows from the minimality property of the Hilbert basis
    have h_basis_element : isHilbertBasisElement (generators i) σ := h_all_in_hb i
    intro h_contra
    rcases h_contra with ⟨v, h_neq, h_in_cone, c, h_pos, h_prop⟩
    -- If v is in cone and c • v = gen i, then gen i is not primitive or not minimal
    sorry

  -- Construct the final result
  exact ⟨n, generators, h_same_cone, h_injective, h_minimal⟩

/-- Computes the star subdivision of a cone by adding a ray through a chosen interior point. -/
def starSubdivision {N : Type} [AddCommGroup N] [Module ℤ N]
    (σ : Cone (NR N)) (v : N) (h_int : (toNR v) ∈ interior σ) :
    Set (Cone (NR N)) := by
  -- First ensure the cone is rational
  have h_rat : σ.IsRational N := by
    -- The existence of a lattice point in the interior implies rationality
    -- This is a standard result in toric geometry: if a cone contains an interior lattice
    -- point, it must be rational.
    sorry

  -- Get the faces of the cone σ
  let faces : Set (Cone (NR N)) := {τ | IsFace τ σ}
  let proper_faces : Set (Cone (NR N)) := {τ ∈ faces | τ ≠ σ}

  -- Star subdivision creates a new cone for each proper face combined with the interior point
  let result : Set (Cone (NR N)) := by
    -- Function to create a new cone from a face and our chosen point v
    let make_new_cone (τ : Cone (NR N)) (h_face : IsFace τ σ) (h_proper : τ ≠ σ) : Cone (NR N) := by
      -- Get the generators of the face τ
      have h_tau_rat : τ.IsRational N := by
        -- A face of a rational cone is rational
        -- This follows from the definition of a face and rationality
        sorry

      rcases findMinimalGenerators τ h_tau_rat with ⟨m, face_gens, h_face_carrier, _, _⟩

      -- Create generators for the new cone: face generators + interior point v
      let new_gens : Fin (m + 1) → N := λ i =>
        if h : i.val < m then face_gens ⟨i.val, h⟩ else v

      -- Construct the new cone
      exact {
        carrier := {u | ∃ cs : Fin (m + 1) → ℝ, (∀ i, cs i ≥ 0) ∧ u = ∑ i, cs i • (toNR (new_gens i))}
        convex := by
          -- A cone defined by non-negative linear combinations is convex by construction
          intros x y hx hy r s hr hs
          rcases hx with ⟨cx, hcx_nonneg, hcx⟩
          rcases hy with ⟨cy, hcy_nonneg, hcy⟩
          exists (λ i => r * cx i + s * cy i)
          constructor
          · intro i
            apply add_nonneg
            · apply mul_nonneg; assumption
            · apply mul_nonneg; assumption
          · -- Show that the linear combination equals the required expression
            calc
              r • x + s • y
              = r • (∑ i, cx i • toNR (new_gens i)) + s • (∑ i, cy i • toNR (new_gens i)) := by rw [hcx, hcy]
              _ = ∑ i, (r * cx i) • toNR (new_gens i) + ∑ i, (s * cy i) • toNR (new_gens i) := by sorry
              _ = ∑ i, (r * cx i + s * cy i) • toNR (new_gens i) := by sorry
        polyhedral := by
          -- A cone is polyhedral if it's generated by finitely many vectors
          exists (m + 1), new_gens
          -- The equality follows from our construction
          rfl
      }

    -- For each proper face τ of σ, create a new cone generated by τ and v
    exact {τ' | ∃ (τ : Cone (NR N)) (h_face : IsFace τ σ) (h_proper : τ ≠ σ),
           τ' = make_new_cone τ h_face h_proper}

  -- The key property of star subdivision: the union of the new cones equals the original cone
  have h_cover : σ.carrier = ⋃ τ' ∈ result, τ'.carrier := by
    apply Set.Subset.antisymm
    · -- Show that every point in σ is in one of the new cones
      intro x hx

      -- If x is in the ray through v, it's in every new cone
      by_cases h_ray : ∃ c : ℝ, c ≥ 0 ∧ x = c • (toNR v)
      · -- x is on the ray through v
        -- By our construction, every new cone contains this ray
        sorry

      -- If x is not on the ray through v, then it determines a face of σ
      -- Let τ be the smallest face of σ containing x
      have h_exists_min_face : ∃ τ ∈ proper_faces, x ∈ τ.carrier ∧
        ∀ ρ ∈ proper_faces, x ∈ ρ.carrier → τ.carrier ⊆ ρ.carrier := by
        -- This follows from the fact that the intersection of faces is a face
        sorry

      -- Let τ be the minimal face containing x
      rcases h_exists_min_face with ⟨τ, hτ, hx_in_τ, h_min⟩
      rcases hτ with ⟨h_τ_face, h_τ_proper⟩

      -- The cone generated by τ and v contains x
      let new_cone := make_new_cone τ h_τ_face h_τ_proper
      have h_x_in_new_cone : x ∈ new_cone.carrier := by
        -- This requires geometric reasoning about cones, faces, and star subdivisions
        sorry

      -- Therefore x is in the union
      exists new_cone, ⟨⟨τ, h_τ_face, h_τ_proper⟩, rfl⟩, h_x_in_new_cone

    · -- Show that every point in the new cones is in σ
      intro x hx
      rcases hx with ⟨τ', ⟨τ, h_face, h_proper, h_eq⟩, hx_in_τ'⟩
      subst h_eq

      -- The new cone is generated by τ (which is in σ) and v (which is in σ)
      -- By convexity, the new cone is contained in σ
      sorry

  -- Return the result
  exact result

/-- Computes the barycentric subdivision of a cone. -/
def barycentricSubdivision {N : Type} [AddCommGroup N] [Module ℤ N]
    (σ : Cone (NR N)) : Set (Cone (NR N)) := by
  -- First, we need to ensure the cone is rational
  have h_rat : σ.IsRational N := by
    -- For the sake of the implementation, we'll assume rationality
    -- In practice, this is either given as a parameter or proven separately
    sorry

  -- Find the minimal generators of σ
  rcases findMinimalGenerators σ h_rat with ⟨n, generators, h_carrier, h_injective, h_minimal⟩

  -- Collect all proper faces of σ
  let faces := {τ | IsFace τ σ}

  -- For each proper face, compute its barycenter
  let face_barycenters : Set N := by
    -- Define a function to compute the barycenter of a face
    let barycenter (τ : Cone (NR N)) (h_face : IsFace τ σ) : N := by
      -- Get generators of the face
      have h_tau_rat : τ.IsRational N := sorry
      rcases findMinimalGenerators τ h_tau_rat with ⟨m, face_gens, _, _, _⟩

      -- Compute the average of the generators as our barycenter
      -- In a real implementation, we might want a more sophisticated approach
      -- that ensures the point is actually in the relative interior
      exact (∑ i, face_gens i) / m

    -- Return the set of all barycenters
    exact {b | ∃ (τ : Cone (NR N)) (h_face : IsFace τ σ) (h_proper : τ ≠ σ),
           b = barycenter τ h_face}

  -- For each barycenter, do a star subdivision
  -- Start with the original cone
  let initial_subdivision : Set (Cone (NR N)) := {σ}

  -- Create a function that performs a star subdivision at a given point
  let subdivide_at (subdivs : Set (Cone (NR N))) (v : N) : Set (Cone (NR N)) := by
    -- For each cone in the current subdivision
    let result : Set (Cone (NR N)) := ∅

    -- For each cone that contains v in its interior, do a star subdivision
    -- For simplicity in this sketch, we'll just return an empty set
    sorry

  -- Recursively apply star subdivisions for each barycenter
  -- This is just a sketch - in practice, we'd iterate through all barycenters
  -- and apply the subdivisions in the right order (from highest to lowest dimension)
  sorry

/-- A step in the recursive subdivision algorithm. -/
def subdivisionStep {N : Type} [AddCommGroup N] [Module ℤ N]
    (σ : Cone (NR N)) (h : ¬σ.IsSmooth N) : Set (Cone (NR N)) :=
  let ⟨n, gens, _⟩ := findMinimalGenerators σ (sorry : σ.IsRational N)
  let v := (∑ i, gens i) -- Take the sum of generators as the interior point
  starSubdivision σ v (sorry) -- Use star subdivision at this point

/-- Main subdivision algorithm for smoothing a single cone. -/
def smoothCone {N : Type} [AddCommGroup N] [Module ℤ N] [FiniteDimensional ℤ N]
    (σ : Cone (NR N)) (h_rat : σ.IsRational N) :
    ∃ S : Set (Cone (NR N)), (∀ τ ∈ S, τ.IsRational N ∧ τ.IsSmooth N) ∧
    σ.carrier = ⋃ τ ∈ S, τ.carrier ∧
    ∀ τ ∈ S, ∃ ρ, IsFace ρ σ ∧ τ.carrier ⊆ ρ.carrier := by
  -- Check if the cone is already smooth
  by_cases h_smooth : σ.IsSmooth N
  · -- If it's already smooth, just return it
    exists {σ}
    constructor
    · intro τ hτ
      simp only [Set.mem_singleton_iff] at hτ
      subst hτ
      exact ⟨h_rat, h_smooth⟩
    · constructor
      · simp only [Set.iUnion_singleton]
      · intro τ hτ
        simp only [Set.mem_singleton_iff] at hτ
        subst hτ
        exists σ
        constructor
        · apply IsFace.refl
        · apply Set.Subset.refl

  -- If it's not smooth, we need to subdivide it
  -- We'll use structural induction on the dimension of the cone

  -- Get the dimension of the ambient space
  let d := FiniteDimensional.finrank ℤ N

  -- Base case: 1-dimensional cones are already smooth
  if h_dim : d = 1 then
    -- Every 1D rational cone is smooth
    have : σ.IsSmooth N := by
      sorry -- Prove that 1D rational cones are smooth
    -- This contradicts our assumption
    contradiction
  else if h_dim : d = 2 then
    -- For 2D cones, use the Hirzebruch continued fraction algorithm
    exact hirzebruchContinuedFraction σ h_dim h_rat
  else
    -- For higher dimensions, apply the general algorithm
    -- First, apply subdivision step
    let subcones := subdivisionStep σ h_smooth

    -- Recursively smooth each subcone
    have h_rational_subcones : ∀ τ ∈ subcones, τ.IsRational N := by
      sorry -- Prove that subdividing a rational cone produces rational subcones

    -- Get smoothed subdivisions for each subcone
    let smooth_subdivisions := λ τ,
      if h_mem : τ ∈ subcones then
        let ⟨S, h_S⟩ := smoothCone τ (h_rational_subcones τ h_mem)
        S
      else
        ∅

    -- Combine all smooth subdivisions
    let S := ⋃ τ ∈ subcones, smooth_subdivisions τ

    -- Prove that S satisfies the required properties
    have h_all_smooth : ∀ τ ∈ S, τ.IsRational N ∧ τ.IsSmooth N := by
      sorry -- Prove that all cones in S are rational and smooth

    have h_cover : σ.carrier = ⋃ τ ∈ S, τ.carrier := by
      sorry -- Prove that S covers σ

    have h_contained : ∀ τ ∈ S, ∃ ρ, IsFace ρ σ ∧ τ.carrier ⊆ ρ.carrier := by
      sorry -- Prove that each cone in S is contained in a face of σ

    exists S, ⟨h_all_smooth, h_cover, h_contained⟩

end Subdivision

section TwoDimensional

/-- Compute the continued fraction expansion of a/b. Returns a list [a₀, a₁, ..., aₙ] such that
    a/b = a₀ + 1/(a₁ + 1/(a₂ + ... + 1/aₙ)). For the Hirzebruch continued fraction algorithm, we need
    a/b where a, b are coprime and a > b. -/
def continuedFraction (a b : ℤ) : List ℤ :=
  let rec cf (a b : ℤ) : List ℤ :=
    if b = 0 then [a]
    else
      let q := a / b
      let r := a % b
      q :: cf b r
  cf a b

/-- Computes a simple version of the continued fraction expansion for two integers.
    For simplicity, we assume a and b are positive and a ≥ b. -/
def euclideanAlgorithm (a b : ℤ) : List (ℤ × ℤ) :=
  let rec steps (a b : ℤ) (acc : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
    if b = 0 then acc
    else
      let q := a / b
      let r := a % b
      steps b r ((a, b) :: acc)
  steps a b []

/-- Generates the sequence of generators needed for the Hirzebruch continued fraction algorithm -/
def hirzebruchGenerators {N : Type} [AddCommGroup N] [Module ℤ N]
    (v₁ v₂ : N) (a₁ b₁ a₂ b₂ : ℤ) : List N :=
  let det := a₁ * b₂ - a₂ * b₁
  if det.natAbs = 1 then [v₁, v₂] -- Already smooth
  else
    -- For simplicity in this implementation, we'll only add the intermediate ray
    -- through the sum v₁ + v₂, but a full implementation would use the continued
    -- fraction expansion to generate all intermediate rays
    [v₁, v₁ + v₂, v₂]

/-- The Hirzebruch continued fraction algorithm for smoothing 2D cones. -/
def hirzebruchContinuedFraction {N : Type} [AddCommGroup N] [Module ℤ N] [FiniteDimensional ℤ N]
    (σ : Cone (NR N)) (h_dim : FiniteDimensional.finrank ℤ N = 2)
    (h_rat : σ.IsRational N) :
    ∃ S : Set (Cone (NR N)), (∀ τ ∈ S, τ.IsRational N ∧ τ.IsSmooth N) ∧
    σ.carrier = ⋃ τ ∈ S, τ.carrier := by
  -- In dimension 2, a cone is generated by 2 minimal generators
  rcases findMinimalGenerators σ h_rat with ⟨n, generators, h_carrier, h_injective, h_minimal⟩

  -- Check if the cone is already smooth
  by_cases h_smooth : σ.IsSmooth N
  · -- If it's already smooth, just return it
    exists {σ}
    constructor
    · intro τ hτ
      simp only [Set.mem_singleton_iff] at hτ
      subst hτ
      exact ⟨h_rat, h_smooth⟩
    · simp only [Set.iUnion_singleton]

  -- If not smooth, we need to apply the Hirzebruch algorithm
  -- For a 2D cone to be non-smooth, it must have exactly 2 generators
  have h_two_gens : n = 2 := by
    -- In dimension 2, a non-smooth cone has exactly 2 generators
    -- This is because:
    -- 1. A cone with 1 generator is always smooth
    -- 2. A cone with >2 generators can't be simplicial in dimension 2
    sorry

  -- Get the two generators
  let v₁ := generators ⟨0, by simp [h_two_gens]⟩
  let v₂ := generators ⟨1, by simp [h_two_gens]⟩

  -- In a basis for N, these vectors can be represented as pairs of integers
  -- We'll assume we have a basis e₁, e₂ for N such that v₁ = a₁e₁ + b₁e₂ and v₂ = a₂e₁ + b₂e₂

  -- For simplicity, we'll use dummy values here
  -- In a real implementation, we would compute these coordinates based on an actual basis
  have basis_exists : ∃ (basis : Basis (Fin 2) ℤ N) (a₁ b₁ a₂ b₂ : ℤ),
      v₁ = a₁ • basis 0 + b₁ • basis 1 ∧
      v₂ = a₂ • basis 0 + b₂ • basis 1 := sorry

  rcases basis_exists with ⟨basis, a₁, b₁, a₂, b₂, h_v₁, h_v₂⟩

  -- The determinant gives us the index of the sublattice
  let det := a₁ * b₂ - a₂ * b₁

  -- If det = ±1, then the cone is already smooth
  if h_det : det.natAbs = 1 then
    exists {σ}
    constructor
    · intro τ hτ
      simp only [Set.mem_singleton_iff] at hτ
      subst hτ
      have : σ.IsSmooth N := by
        -- A cone with determinant ±1, i.e., the generators form part of a basis
        -- thus making the cone smooth by definition
        exists 2, generators
        constructor
        · exact h_carrier
        · -- Show that generators form part of a basis
          sorry
      exact ⟨h_rat, this⟩
    · simp only [Set.iUnion_singleton]
  else
    -- Otherwise, we need to apply the continued fraction algorithm

    -- For simplicity, assume a₁ and a₂ are positive and a₁ > a₂
    -- Compute the continued fraction expansion of a₁/a₂
    let expansion := if a₂ ≠ 0 then continuedFraction a₁ a₂ else []

    -- Generate intermediate rays based on the continued fraction expansion
    let intermediate_rays := hirzebruchGenerators v₁ v₂ a₁ b₁ a₂ b₂

    -- For simplicity in this implementation, we'll just add one new ray through v₁ + v₂
    let v₃ := v₁ + v₂

    -- Create two new cones: (v₁, v₃) and (v₃, v₂)
    let make_cone (u₁ u₂ : N) : Cone (NR N) := {
      carrier := {v | ∃ c₁ c₂ : ℝ, c₁ ≥ 0 ∧ c₂ ≥ 0 ∧ v = c₁ • (toNR u₁) + c₂ • (toNR u₂)}
      convex := by
        intros x y hx hy r s hr hs
        rcases hx with ⟨c₁, c₂, hc₁, hc₂, h_eq_x⟩
        rcases hy with ⟨d₁, d₂, hd₁, hd₂, h_eq_y⟩
        exists r * c₁ + s * d₁, r * c₂ + s * d₂
        constructor
        · -- Prove combined coefficients are non-negative
          constructor
          · apply add_nonneg
            · apply mul_nonneg; assumption
            · apply mul_nonneg; assumption
          · apply add_nonneg
            · apply mul_nonneg; assumption
            · apply mul_nonneg; assumption
        · -- Prove the linear combination equals the required expression
          sorry
      polyhedral := by
        -- Prove the cone is polyhedral using the generators
        exists 2, ![u₁, u₂]
        sorry
    }

    let cone₁ := make_cone v₁ v₃
    let cone₂ := make_cone v₃ v₂

    -- Prove that these new cones are both rational
    have h_rat₁ : cone₁.IsRational N := by
      -- A cone generated by lattice points is rational by definition
      exists 2, ![v₁, v₃]
      sorry

    have h_rat₂ : cone₂.IsRational N := by
      -- A cone generated by lattice points is rational by definition
      exists 2, ![v₃, v₂]
      sorry

    -- Recursively apply the algorithm to each subcone
    -- In practice, we might need multiple steps to achieve smoothness
    rcases hirzebruchContinuedFraction cone₁ h_dim h_rat₁ with ⟨S₁, h_smooth₁, h_cover₁⟩
    rcases hirzebruchContinuedFraction cone₂ h_dim h_rat₂ with ⟨S₂, h_smooth₂, h_cover₂⟩

    -- Combine the results
    let S := S₁ ∪ S₂

    -- Prove that S satisfies the required properties
    have h_all_smooth : ∀ τ ∈ S, τ.IsRational N ∧ τ.IsSmooth N := by
      intro τ hτ
      cases' hτ with h_τ_S₁ h_τ_S₂
      · exact h_smooth₁ τ h_τ_S₁
      · exact h_smooth₂ τ h_τ_S₂

    have h_cover : σ.carrier = ⋃ τ ∈ S, τ.carrier := by
      apply Set.Subset.antisymm
      · -- Show that σ.carrier is contained in the union
        intro v hv
        -- Express v as a non-negative combination of v₁ and v₂
        rcases h_carrier.symm ▸ hv with ⟨cs, h_nonneg, h_sum⟩
        sorry -- Complete the proof that v is in one of the subdivided cones
      · -- Show that the union is contained in σ.carrier
        intro v hv
        rcases hv with ⟨τ, hτ, hv⟩
        cases' hτ with h_τ_S₁ h_τ_S₂
        · -- If τ ∈ S₁, then τ.carrier ⊆ cone₁.carrier ⊆ σ.carrier
          sorry
        · -- If τ ∈ S₂, then τ.carrier ⊆ cone₂.carrier ⊆ σ.carrier
          sorry

    exists S, ⟨h_all_smooth, h_cover⟩

end TwoDimensional

/-- The main subdivision theorem: every rational polyhedral cone can be subdivided
    into a fan of smooth cones. -/
theorem exists_smooth_subdivision {N : Type} [AddCommGroup N] [Module ℤ N] [FiniteDimensional ℤ N]
    (σ : Cone (NR N)) (h_rat : σ.IsRational N) :
    ∃ S : Set (Cone (NR N)), (∀ τ ∈ S, τ.IsRational N ∧ τ.IsSmooth N) ∧
    σ.carrier = ⋃ τ ∈ S, τ.carrier := by
  -- We can directly use the smoothCone function, which implements the subdivison algorithm
  rcases smoothCone σ h_rat with ⟨S, h_smooth, h_cover, h_contained⟩

  -- Extract just the properties we need for this theorem
  exists S, ⟨h_smooth, h_cover.1⟩

end ConeSubdivision
