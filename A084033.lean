import A084030

/-! # A084033 — corollaire d'A084029 (triangle des quotients)

Texte OEIS verbatim : « Triangle read by rows:
T(n, k) = A084029(n, k)/n. »
Données : 1,10,0,34,37,40,253,280,325,505,2008,…
(pas de conjecture sur la fiche.)

Fidélité de l'énoncé validée à l'aveugle par argon
(A084030/VERIFICATIONS/A084030-resp.txt, verdict VRAI) :
l'image par (·/n) = les quotients, injective sur les multiples
de n ; chaque quotient est non nul car N ≥ 10^(n-1) > n pour
n ≥ 3. -/

namespace A084033

/-- La division exacte par n est injective sur les multiples de n. -/
private theorem div_injOn {n : ℕ} (_hn : 0 < n) :
    Set.InjOn (· / n) {N : ℕ | n ∣ N} := by
  intro a ha b hb h
  have h2 : a / n = b / n := h
  calc a = n * (a / n) := (Nat.mul_div_cancel' ha).symm
    _ = n * (b / n) := by rw [h2]
    _ = b := Nat.mul_div_cancel' hb

end A084033

open A084030 in
open A084033 in
/-- A084033 — T(n,k) = A084029(n,k)/n : pour n ≥ 3 la ligne des
    quotients a ≥ n termes, tous non nuls (division exacte). -/
theorem A084033 (n : ℕ) (hn : 3 ≤ n) :
    n ≤ ((witnesses n).image (· / n)).card ∧
      ∀ q ∈ (witnesses n).image (· / n), 0 < q := by
  have hinj : Set.InjOn (· / n) ↑(witnesses n) :=
    (div_injOn (by omega : 0 < n)).mono fun N hN =>
      (Finset.mem_filter.mp hN).2.1
  refine ⟨?_, ?_⟩
  · calc n ≤ (witnesses n).card := card_witnesses_ge n hn
      _ = ((witnesses n).image (· / n)).card :=
          (Finset.card_image_of_injOn hinj).symm
  · rintro q hq
    obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hq
    have hf := Finset.mem_filter.mp hN
    have hdvd : n ∣ N := hf.2.1
    have hlen : (Nat.digits 10 N).length = n := hf.2.2.1
    have hpos : 0 < N := by
      have hne : Nat.digits 10 N ≠ [] := by
        intro e
        rw [e, List.length_nil] at hlen
        omega
      exact Nat.pos_of_ne_zero fun hN0 =>
        hne (hN0 ▸ Nat.digits_zero 10)
    exact Nat.div_pos (Nat.le_of_dvd hpos hdvd) (by omega)

#print axioms A084033
